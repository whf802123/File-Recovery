import argparse
import csv
import io
import mmap
import os
import struct
import tarfile
import zipfile
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path

@dataclass
class RecoveredFile:
    filename: str
    file_type: str
    start_offset: int
    end_offset: int
    file_size: int
    sha256_hash: str

HEADERS = {
    "pdf": [b"%PDF"],
    "jpg": [b"\xFF\xD8\xFF"],
    "png": [b"\x89PNG\r\n\x1A\n"],
    "gif": [b"GIF87a", b"GIF89a"],
    "bmp": [b"BM"],
    "mpg": [b"\x00\x00\x01\xB3"],
    "avi": [b"RIFF"],
    "wav": [b"RIFF"],
    "zip": [b"PK\x03\x04"],
    "rar": [b"Rar!\x1A\x07\x00", b"Rar!\x1A\x07\x01\x00"],
    "7z": [b"7z\xBC\xAF\x27\x1C"],
    "gz": [b"\x1F\x8B\x08"],
    "tar": [b"ustar"],
    "mp3": [b"ID3"],
    "flac": [b"fLaC"],
    "mp4": [b"ftyp"],
    "mov": [b"ftyp"],
    "exe": [b"MZ"],
    "elf": [b"\x7FELF"],
    "sqlite": [b"SQLite format 3\x00"],
}

FOOTERS = {
    "pdf": b"%%EOF",
    "jpg": b"\xFF\xD9",
    "png": b"IEND\xAE\x42\x60\x82",
    "gif": b"\x3B",
    "mpg": b"\x00\x00\x01\xB7",
}

ZIP_EOCD = b"PK\x05\x06"

class FileSignatureCarver:
    def __init__(self, disk_data, output_dir: Path, selected_types=None, max_scan_size=512 * 1024 * 1024):
        self.disk_data = disk_data
        self.output_dir = output_dir
        self.selected_types = set(selected_types) if selected_types else set(HEADERS.keys())
        self.max_scan_size = max_scan_size
        self.recovered = []
        self.seen_ranges = set()

    def carve(self):
        self.output_dir.mkdir(parents=True, exist_ok=True)

        for file_type, header_list in HEADERS.items():
            if file_type not in self.selected_types:
                continue

            for header in header_list:
                self._scan_for_type(file_type, header)

        self._write_manifest()
        return self.recovered

    def _scan_for_type(self, file_type, header):
        offset = 0

        while True:
            offset = self.disk_data.find(header, offset)

            if offset == -1:
                break

            if file_type in {"tar", "mp4", "mov"}:
                real_offset = self._adjust_offset(file_type, offset)
                if real_offset is None:
                    offset += len(header)
                    continue
                offset = real_offset

            end_offset = self._find_end_offset(file_type, offset)

            if end_offset is None or end_offset <= offset:
                offset += len(header)
                continue

            if end_offset > len(self.disk_data):
                offset += len(header)
                continue

            file_data = self.disk_data[offset:end_offset]

            if not self._looks_valid(file_type, file_data):
                offset += len(header)
                continue

            real_type = self._detect_real_type(file_type, file_data)
            self._save_file(real_type, offset, end_offset, file_data)

            offset = end_offset

    def _adjust_offset(self, file_type, offset):
        if file_type == "tar":
            possible_start = offset - 257
            if possible_start >= 0:
                return possible_start
            return None

        if file_type in {"mp4", "mov"}:
            possible_start = offset - 4
            if possible_start >= 0:
                return possible_start
            return None

        return offset

    def _find_end_offset(self, file_type, offset):
        if file_type == "bmp":
            return self._find_bmp_end(offset)

        if file_type in {"avi", "wav"}:
            return self._find_riff_end(offset, file_type)

        if file_type == "zip":
            return self._find_zip_end(offset)

        if file_type == "rar":
            return self._find_next_header_based_end(offset)

        if file_type == "7z":
            return self._find_7z_end(offset)

        if file_type == "gz":
            return self._find_gz_end(offset)

        if file_type == "tar":
            return self._find_tar_end(offset)

        if file_type == "mp3":
            return self._find_mp3_end(offset)

        if file_type == "flac":
            return self._find_next_header_based_end(offset)

        if file_type in {"mp4", "mov"}:
            return self._find_mp4_end(offset)

        if file_type == "exe":
            return self._find_pe_end(offset)

        if file_type == "elf":
            return self._find_elf_end(offset)

        if file_type == "sqlite":
            return self._find_sqlite_end(offset)

        footer = FOOTERS.get(file_type)
        if not footer:
            return None

        footer_offset = self.disk_data.find(footer, offset + len(HEADERS[file_type][0]))

        if footer_offset == -1:
            return None

        if file_type == "pdf":
            search_end = min(footer_offset + 2048, len(self.disk_data))
            later_footer = self.disk_data.rfind(footer, offset, search_end)
            if later_footer != -1:
                footer_offset = later_footer

        return footer_offset + len(footer)

    def _find_bmp_end(self, offset):
        if offset + 10 > len(self.disk_data):
            return None

        size_bytes = self.disk_data[offset + 2:offset + 6]
        reserved_bytes = self.disk_data[offset + 6:offset + 10]

        if reserved_bytes != b"\x00\x00\x00\x00":
            return None

        file_size = int.from_bytes(size_bytes, byteorder="little")

        if file_size < 54:
            return None

        return offset + file_size

    def _find_riff_end(self, offset, expected_type):
        if offset + 12 > len(self.disk_data):
            return None

        if self.disk_data[offset:offset + 4] != b"RIFF":
            return None

        riff_type = self.disk_data[offset + 8:offset + 12]

        if expected_type == "avi" and riff_type != b"AVI ":
            return None

        if expected_type == "wav" and riff_type != b"WAVE":
            return None

        size = int.from_bytes(self.disk_data[offset + 4:offset + 8], byteorder="little")
        file_size = size + 8

        if file_size < 12:
            return None

        return offset + file_size

    def _find_zip_end(self, offset):
        search_offset = offset

        while True:
            eocd_offset = self.disk_data.find(ZIP_EOCD, search_offset)

            if eocd_offset == -1:
                return None

            if eocd_offset + 22 > len(self.disk_data):
                return None

            comment_length = int.from_bytes(
                self.disk_data[eocd_offset + 20:eocd_offset + 22],
                byteorder="little",
            )

            end_offset = eocd_offset + 22 + comment_length

            if end_offset <= len(self.disk_data):
                possible_zip = self.disk_data[offset:end_offset]
                if self._is_valid_zip(possible_zip):
                    return end_offset

            search_offset = eocd_offset + len(ZIP_EOCD)

    def _find_7z_end(self, offset):
        if offset + 32 > len(self.disk_data):
            return None

        next_header_offset = int.from_bytes(self.disk_data[offset + 12:offset + 20], "little")
        next_header_size = int.from_bytes(self.disk_data[offset + 20:offset + 28], "little")

        file_size = 32 + next_header_offset + next_header_size

        if file_size < 32:
            return None

        return offset + file_size

    def _find_gz_end(self, offset):
        next_offsets = []

        for headers in HEADERS.values():
            for header in headers:
                found = self.disk_data.find(header, offset + 3)
                if found != -1:
                    next_offsets.append(found)

        max_end = min(offset + self.max_scan_size, len(self.disk_data))

        if next_offsets:
            return min(min(next_offsets), max_end)

        return max_end

    def _find_tar_end(self, offset):
        try:
            max_end = min(offset + self.max_scan_size, len(self.disk_data))
            data = self.disk_data[offset:max_end]

            with tarfile.open(fileobj=io.BytesIO(data), mode="r:*") as tf:
                members = tf.getmembers()

                if not members:
                    return None

                last_end = 0

                for member in members:
                    member_data_end = member.offset_data + member.size
                    padded_end = ((member_data_end + 511) // 512) * 512
                    last_end = max(last_end, padded_end)

                return offset + last_end + 1024

        except Exception:
            return None

    def _find_mp3_end(self, offset):
        if self.disk_data[offset:offset + 3] != b"ID3":
            return None

        if offset + 10 > len(self.disk_data):
            return None

        size_bytes = self.disk_data[offset + 6:offset + 10]
        tag_size = (
            ((size_bytes[0] & 0x7F) << 21)
            | ((size_bytes[1] & 0x7F) << 14)
            | ((size_bytes[2] & 0x7F) << 7)
            | (size_bytes[3] & 0x7F)
        )

        search_start = offset + 10 + tag_size
        end = self._find_next_header_based_end(offset, start=search_start)

        return end

    def _find_mp4_end(self, offset):
        current = offset
        end = offset
        limit = min(offset + self.max_scan_size, len(self.disk_data))

        while current + 8 <= limit:
            atom_size = int.from_bytes(self.disk_data[current:current + 4], "big")
            atom_type = self.disk_data[current + 4:current + 8]

            if atom_size == 0:
                return limit

            if atom_size == 1:
                if current + 16 > limit:
                    return None
                atom_size = int.from_bytes(self.disk_data[current + 8:current + 16], "big")

            if atom_size < 8:
                break

            if not all(32 <= b <= 126 for b in atom_type):
                break

            end = current + atom_size
            current = end

            if atom_type in {b"mdat", b"moov"} and current > offset + 32:
                continue

        if end > offset + 8:
            return end

        return None

    def _find_pe_end(self, offset):
        if offset + 0x40 > len(self.disk_data):
            return None

        if self.disk_data[offset:offset + 2] != b"MZ":
            return None

        pe_offset = int.from_bytes(self.disk_data[offset + 0x3C:offset + 0x40], "little")

        if pe_offset <= 0 or offset + pe_offset + 24 > len(self.disk_data):
            return None

        if self.disk_data[offset + pe_offset:offset + pe_offset + 4] != b"PE\x00\x00":
            return None

        coff_offset = offset + pe_offset + 4
        number_of_sections = int.from_bytes(self.disk_data[coff_offset + 2:coff_offset + 4], "little")
        size_of_optional_header = int.from_bytes(self.disk_data[coff_offset + 16:coff_offset + 18], "little")

        section_table = coff_offset + 20 + size_of_optional_header
        max_end = 0

        for i in range(number_of_sections):
            section_offset = section_table + i * 40

            if section_offset + 40 > len(self.disk_data):
                return None

            size_of_raw_data = int.from_bytes(self.disk_data[section_offset + 16:section_offset + 20], "little")
            pointer_to_raw_data = int.from_bytes(self.disk_data[section_offset + 20:section_offset + 24], "little")

            max_end = max(max_end, pointer_to_raw_data + size_of_raw_data)

        if max_end <= 0:
            return None

        return offset + max_end

    def _find_elf_end(self, offset):
        if offset + 64 > len(self.disk_data):
            return None

        if self.disk_data[offset:offset + 4] != b"\x7FELF":
            return None

        elf_class = self.disk_data[offset + 4]
        endian = self.disk_data[offset + 5]

        if endian == 1:
            byteorder = "little"
        elif endian == 2:
            byteorder = "big"
        else:
            return None

        if elf_class == 1:
            e_shoff_offset = 32
            e_shentsize_offset = 46
            e_shnum_offset = 48
            header_min = 52
        elif elf_class == 2:
            e_shoff_offset = 40
            e_shentsize_offset = 58
            e_shnum_offset = 60
            header_min = 64
        else:
            return None

        if offset + header_min > len(self.disk_data):
            return None

        if elf_class == 1:
            section_header_offset = int.from_bytes(self.disk_data[offset + e_shoff_offset:offset + e_shoff_offset + 4], byteorder)
        else:
            section_header_offset = int.from_bytes(self.disk_data[offset + e_shoff_offset:offset + e_shoff_offset + 8], byteorder)

        section_entry_size = int.from_bytes(self.disk_data[offset + e_shentsize_offset:offset + e_shentsize_offset + 2], byteorder)
        section_count = int.from_bytes(self.disk_data[offset + e_shnum_offset:offset + e_shnum_offset + 2], byteorder)

        if section_header_offset == 0 or section_entry_size == 0 or section_count == 0:
            return None

        file_size = section_header_offset + section_entry_size * section_count

        if file_size < header_min:
            return None

        return offset + file_size

    def _find_sqlite_end(self, offset):
        if offset + 100 > len(self.disk_data):
            return None

        if self.disk_data[offset:offset + 16] != b"SQLite format 3\x00":
            return None

        page_size = int.from_bytes(self.disk_data[offset + 16:offset + 18], "big")

        if page_size == 1:
            page_size = 65536

        if page_size < 512 or page_size > 65536:
            return None

        page_count = int.from_bytes(self.disk_data[offset + 28:offset + 32], "big")

        if page_count <= 0:
            return None

        file_size = page_size * page_count

        return offset + file_size

    def _find_next_header_based_end(self, offset, start=None):
        search_start = start or offset + 1
        candidates = []

        for file_type, headers in HEADERS.items():
            for header in headers:
                found = self.disk_data.find(header, search_start)
                if found != -1:
                    candidates.append(found)

        max_end = min(offset + self.max_scan_size, len(self.disk_data))

        if not candidates:
            return max_end

        return min(min(candidates), max_end)

    def _looks_valid(self, file_type, file_data):
        if len(file_data) == 0:
            return False

        if file_type == "pdf":
            return file_data.startswith(b"%PDF") and b"%%EOF" in file_data[-4096:]

        if file_type == "jpg":
            return file_data.startswith(b"\xFF\xD8\xFF") and file_data.endswith(b"\xFF\xD9")

        if file_type == "png":
            return file_data.startswith(b"\x89PNG\r\n\x1A\n") and file_data.endswith(b"IEND\xAE\x42\x60\x82")

        if file_type == "gif":
            return file_data.startswith((b"GIF87a", b"GIF89a")) and file_data.endswith(b"\x3B")

        if file_type == "bmp":
            return file_data.startswith(b"BM") and len(file_data) >= 54

        if file_type == "avi":
            return file_data.startswith(b"RIFF") and file_data[8:12] == b"AVI "

        if file_type == "wav":
            return file_data.startswith(b"RIFF") and file_data[8:12] == b"WAVE"

        if file_type == "zip":
            return self._is_valid_zip(file_data)

        if file_type == "rar":
            return file_data.startswith((b"Rar!\x1A\x07\x00", b"Rar!\x1A\x07\x01\x00"))

        if file_type == "7z":
            return file_data.startswith(b"7z\xBC\xAF\x27\x1C")

        if file_type == "gz":
            return file_data.startswith(b"\x1F\x8B\x08")

        if file_type == "tar":
            return len(file_data) >= 512 and file_data[257:262] == b"ustar"

        if file_type == "mp3":
            return file_data.startswith(b"ID3")

        if file_type == "flac":
            return file_data.startswith(b"fLaC")

        if file_type in {"mp4", "mov"}:
            return len(file_data) >= 12 and file_data[4:8] == b"ftyp"

        if file_type == "exe":
            return file_data.startswith(b"MZ") and b"PE\x00\x00" in file_data[:4096]

        if file_type == "elf":
            return file_data.startswith(b"\x7FELF")

        if file_type == "sqlite":
            return file_data.startswith(b"SQLite format 3\x00")

        return True

    def _is_valid_zip(self, file_data):
        try:
            with zipfile.ZipFile(io.BytesIO(file_data)) as zf:
                zf.testzip()
            return True
        except Exception:
            return False

    def _detect_real_type(self, file_type, file_data):
        if file_type == "zip":
            return self._detect_zip_based_type(file_data)

        if file_type in {"avi", "wav"}:
            if file_data[8:12] == b"AVI ":
                return "avi"
            if file_data[8:12] == b"WAVE":
                return "wav"

        if file_type in {"mp4", "mov"}:
            major_brand = file_data[8:12]
            if major_brand in {b"qt  "}:
                return "mov"
            return "mp4"

        return file_type

    def _detect_zip_based_type(self, file_data):
        try:
            with zipfile.ZipFile(io.BytesIO(file_data)) as zf:
                names = set(zf.namelist())

            if "[Content_Types].xml" in names and "word/document.xml" in names:
                return "docx"

            if "[Content_Types].xml" in names and "xl/workbook.xml" in names:
                return "xlsx"

            if "[Content_Types].xml" in names and "ppt/presentation.xml" in names:
                return "pptx"

            if "AndroidManifest.xml" in names:
                return "apk"

            if any(name.endswith(".class") for name in names):
                return "jar"

            return "zip"

        except Exception:
            return "zip"

    def _save_file(self, file_type, start_offset, end_offset, file_data):
        file_range = (start_offset, end_offset)

        if file_range in self.seen_ranges:
            return

        self.seen_ranges.add(file_range)

        file_size = end_offset - start_offset
        file_hash = sha256(file_data).hexdigest()

        index = len(self.recovered) + 1
        filename = f"recovered_{index:04d}_{start_offset:010d}.{file_type}"
        output_path = self.output_dir / filename

        with open(output_path, "wb") as f:
            f.write(file_data)

        self.recovered.append(
            RecoveredFile(
                filename=filename,
                file_type=file_type,
                start_offset=start_offset,
                end_offset=end_offset,
                file_size=file_size,
                sha256_hash=file_hash,
            )
        )

    def _write_manifest(self):
        manifest_path = self.output_dir / "manifest.csv"

        with open(manifest_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)

            writer.writerow([
                "filename",
                "file_type",
                "start_offset",
                "end_offset",
                "file_size",
                "sha256",
            ])

            for item in self.recovered:
                writer.writerow([
                    item.filename,
                    item.file_type,
                    item.start_offset,
                    item.end_offset,
                    item.file_size,
                    item.sha256_hash,
                ])

def parse_args():
    parser = argparse.ArgumentParser(
        description="Recover files from a disk image using file signatures."
    )

    parser.add_argument(
        "disk_image",
        help="Path to disk image or raw binary file."
    )

    parser.add_argument(
        "-o",
        "--output",
        default="recovered_files",
        help="Output directory. Default: recovered_files"
    )

    parser.add_argument(
        "-t",
        "--types",
        nargs="+",
        choices=sorted(HEADERS.keys()),
        help="File types to recover. Example: -t pdf jpg png zip mp4 sqlite"
    )

    parser.add_argument(
        "--max-scan-size",
        type=int,
        default=512 * 1024 * 1024,
        help="Maximum scan size for formats without reliable footer. Default: 536870912"
    )

    return parser.parse_args()

def main():
    args = parse_args()

    disk_path = Path(args.disk_image)
    output_dir = Path(args.output)

    if not disk_path.is_file():
        raise FileNotFoundError(f"Disk image not found: {disk_path}")

    with open(disk_path, "rb") as f:
        with mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as disk_data:
            carver = FileSignatureCarver(
                disk_data=disk_data,
                output_dir=output_dir,
                selected_types=args.types,
                max_scan_size=args.max_scan_size,
            )

            recovered = carver.carve()

    print(f"Recovered files: {len(recovered)}")
    print(f"Output directory: {output_dir}")
    print(f"Manifest: {output_dir / 'manifest.csv'}")

    if recovered:
        print()
        print("Filename\tType\tStart\tEnd\tSize\tSHA-256")

        for item in recovered:
            print(
                f"{item.filename}\t"
                f"{item.file_type}\t"
                f"{item.start_offset}\t"
                f"{item.end_offset}\t"
                f"{item.file_size}\t"
                f"{item.sha256_hash}"
            )

if __name__ == "__main__":
    main()

