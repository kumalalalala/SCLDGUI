"""
SoundCloud Music Downloader (SCDL Pro GUI - Monolithic Standalone Edition)
Một tệp thực thi duy nhất, độc lập hoàn toàn, tích hợp sẵn toàn bộ lõi SCDL và giao diện Tkinter hiện đại.
Hỗ trợ đầy đủ 100% tính năng của SCDL CLI, bao gồm tải từ bài số mấy (offset/range), đa luồng tăng tốc và giám sát thời gian thực.
"""

import base64
import collections
import configparser
import contextlib
import email.message
import errno
import functools
import importlib
import json
import logging
import os
import platform
import posixpath
import queue
import re
import shlex
import subprocess
import sys
import threading
import urllib.parse
from pathlib import Path
from typing import ClassVar, Optional

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# ==============================================================================
# KIỂM TRA THƯ VIỆN PHỤ THUỘC
# ==============================================================================
MISSING_DEPS = []

try:
    import mutagen
    from mutagen import FileType, aiff, dsdiff, dsf, flac, id3, mp3, mp4, oggopus, oggspeex, oggtheora, oggvorbis, trueaudio, wave
    MUTAGEN_AVAILABLE = True
except ImportError:
    MUTAGEN_AVAILABLE = False
    MISSING_DEPS.append("mutagen")

try:
    from soundcloud import AlbumPlaylist, SoundCloud, Track, User
    SOUNDCLOUD_AVAILABLE = True
except ImportError:
    SOUNDCLOUD_AVAILABLE = False
    MISSING_DEPS.append("soundcloud-v2")

try:
    import yt_dlp
    from yt_dlp import YoutubeDL
    from yt_dlp.YoutubeDL import _catch_unsafe_extension_error
    from yt_dlp.compat import imghdr
    from yt_dlp.networking.common import Request, Response
    from yt_dlp.postprocessor.common import PostProcessor
    from yt_dlp.utils import (
        OUTTMPL_TYPES,
        DownloadCancelled,
        PostProcessingError,
        date_from_str,
        locked_file,
        replace_extension,
        variadic,
    )
    import yt_dlp.options as ytdl_options
    YTDLP_AVAILABLE = True
except ImportError:
    YTDLP_AVAILABLE = False
    MISSING_DEPS.append("yt-dlp")

    class DownloadCancelled(Exception):
        pass


# ==============================================================================
# PHẦN 1: BỘ TIỀN / HẬU XỬ LÝ VÀ PATCH CỦA SCDL (EMBEDDED SCDL ENGINE PATCHES)
# ==============================================================================

class AbortDownloadException(DownloadCancelled):
    """Ngoại lệ phát sinh khi người dùng chủ động nhấn Hủy Tải."""
    pass


if YTDLP_AVAILABLE:
    # 1. Patch Old Archive IDs
    def _in_download_archive_patched(self, info_dict):
        if not self.archive:
            return False
        vid_ids = [self._make_archive_id(info_dict)]
        vid_ids.extend(info_dict.get("_old_archive_ids") or [])
        return any(id_ in self.archive for id_ in vid_ids) or any(id_.split()[1] in self.archive for id_ in vid_ids if id_)

    YoutubeDL.in_download_archive = _in_download_archive_patched

    # 2. Patch Thumbnail Selection
    def _sort_thumbnails_patched(self, thumbnails):
        thumbnails.sort(
            key=lambda t: (
                t.get("id") == self.params.get("thumbnail_id") if t.get("id") is not None else False,
                t.get("preference") if t.get("preference") is not None else -1,
                t.get("width") if t.get("width") is not None else -1,
                t.get("height") if t.get("height") is not None else -1,
                t.get("id") if t.get("id") is not None else "",
                t.get("url"),
            )
        )

    YoutubeDL._sort_thumbnails = _sort_thumbnails_patched

    _old_parse_options = yt_dlp.parse_options

    def _parse_options_patched(argv=None):
        parsed = _old_parse_options(argv)
        if len(parsed) > 3 and hasattr(parsed[1], "thumbnail_id"):
            parsed[3]["thumbnail_id"] = parsed[1].thumbnail_id
        return parsed

    yt_dlp.parse_options = _parse_options_patched

    _old_create_parser = ytdl_options.create_parser

    def _create_parser_patched():
        parser = _old_create_parser()
        thumbnail_group = parser.get_option_group("--write-thumbnail")
        if thumbnail_group:
            thumbnail_group.add_option("--thumbnail-id", metavar="ID", dest="thumbnail_id", help="ID of thumbnail to write")
        trim_group = parser.get_option_group("--trim-filenames")
        if trim_group:
            trim_group.remove_option("--trim-filenames")
            trim_group.add_option(
                "--trim-filenames",
                "--trim-file-names",
                metavar="LENGTH",
                dest="trim_file_name",
                default="none",
                help="Limit filename length in characters or bytes",
            )
        return parser

    ytdl_options.create_parser = _create_parser_patched

    # 3. Patch Trim Filenames
    def _evaluate_outtmpl_patched(self, outtmpl, info_dict, *args, trim_filename=False, **kwargs):
        outtmpl, info_dict = self.prepare_outtmpl(outtmpl, info_dict, *args, **kwargs)
        if not trim_filename:
            return self.escape_outtmpl(outtmpl) % info_dict

        ext_suffix = ".%(ext\0s)s"
        suffix = ""
        if outtmpl.endswith(ext_suffix):
            outtmpl = outtmpl[: -len(ext_suffix)]
            suffix = ext_suffix % info_dict
        outtmpl = self.escape_outtmpl(outtmpl)
        filename = outtmpl % info_dict

        def parse_trim_file_name(trim_name):
            if trim_name is None or trim_name == "none":
                return 0, None
            mobj = re.match(r"(?:(?P<length>\d+)(?P<mode>b|c)?|none)", str(trim_name))
            if not mobj:
                return 0, None
            return int(mobj.group("length")), mobj.group("mode") or "c"

        max_file_name, mode = parse_trim_file_name(self.params.get("trim_file_name"))
        if max_file_name == 0:
            return filename + suffix

        encoding = sys.getfilesystemencoding() if platform.system() != "Windows" else "utf-16-le"

        def trim_part(name: str):
            if mode == "b":
                encoded = name.encode(encoding)
                encoded = encoded[:max_file_name]
                return encoded.decode(encoding, "ignore")
            return name[:max_file_name]

        filename = os.path.join(*map(trim_part, Path(filename).parts or "."))
        return filename + suffix

    @_catch_unsafe_extension_error
    def _prepare_filename_patched(self, info_dict, *, outtmpl=None, tmpl_type=None):
        assert None in (outtmpl, tmpl_type), "outtmpl and tmpl_type are mutually exclusive"
        if outtmpl is None:
            outtmpl = self.params["outtmpl"].get(tmpl_type or "default", self.params["outtmpl"]["default"])
        try:
            outtmpl = self._outtmpl_expandpath(outtmpl)
            filename = self.evaluate_outtmpl(outtmpl, info_dict, True, trim_filename=True)
            if not filename:
                return None
            if tmpl_type in ("", "temp"):
                final_ext, ext = self.params.get("final_ext"), info_dict.get("ext")
                if final_ext and ext and final_ext != ext and filename.endswith(f".{final_ext}"):
                    filename = replace_extension(filename, ext, final_ext)
            elif tmpl_type:
                force_ext = OUTTMPL_TYPES[tmpl_type]
                if force_ext:
                    filename = replace_extension(filename, force_ext, info_dict.get("ext"))
            return filename
        except ValueError as err:
            self.report_error("Error in output template: " + str(err))
            return None

    YoutubeDL.evaluate_outtmpl = _evaluate_outtmpl_patched
    YoutubeDL._prepare_filename = _prepare_filename_patched

    # 4. OuttmplPP (Switch outtmpl between playlist & single track)
    class OuttmplPP(PostProcessor):
        def __init__(self, video_outtmpl: str, playlist_outtmpl: str, downloader=None):
            super().__init__(downloader)
            self._outtmpls = {False: video_outtmpl, True: playlist_outtmpl}

        def run(self, info):
            if getattr(self._downloader, "_abort_event", None) and self._downloader._abort_event.is_set():
                raise AbortDownloadException("Người dùng đã hủy quá trình tải.")
            in_playlist = info.get("playlist_uploader") is not None
            self._downloader.params["outtmpl"]["default"] = self._outtmpls[in_playlist]
            if not in_playlist:
                for meta in ("track", "album_artist", "album"):
                    info[f"meta_{meta}"] = None
            return [], info

    # 5. OriginalFilenamePP (Preserve original filename when downloading original audio)
    def _parse_header(content_disposition):
        if not content_disposition:
            return {}
        message = email.message.Message()
        message["content-type"] = content_disposition
        return dict(message.get_params({}))

    class OriginalFilenamePP(PostProcessor):
        def run(self, info):
            if getattr(self._downloader, "_abort_event", None) and self._downloader._abort_event.is_set():
                raise AbortDownloadException("Người dùng đã hủy quá trình tải.")
            for format_dict in info.get("formats", ()):
                if format_dict.get("format_id") == "download":
                    res = self._downloader.urlopen(Request(format_dict["url"], headers=format_dict["http_headers"]))
                    params = _parse_header(res.get_header("content-disposition"))
                    if "filename" not in params:
                        break
                    filename = urllib.parse.unquote(params["filename"][-1], encoding="utf-8")
                    old_outtmpl = self._downloader.params["outtmpl"]["default"]
                    self._downloader.params["outtmpl"]["default"] = (
                        Path(old_outtmpl).with_name(filename).with_suffix(".%(ext)s").as_posix()
                    )
                    break
            return [], info

    # 6. SyncDownloadHelper (Synchronize downloaded tracks against archive file)
    class SyncDownloadHelper:
        def __init__(self, scdl_args, ydl: YoutubeDL):
            self._ydl = ydl
            self._enabled = bool(scdl_args.get("sync"))
            self._sync_file = scdl_args.get("sync")
            self._all_files: dict[str, Path] = {}
            self._downloaded: set[str] = set()
            self._init()

        def _init(self):
            if not self._enabled:
                return

            def track_downloaded(d):
                if d["status"] != "finished":
                    return
                info = d["info_dict"]
                id_ = f"soundcloud {info['id']}"
                self._downloaded.add(id_)
                self._all_files[id_] = d["filename"]

            self._ydl.add_progress_hook(track_downloaded)

            try:
                with locked_file(self._sync_file, "r", encoding="utf-8") as archive_file:
                    for line in archive_file:
                        line = line.strip()
                        if not line:
                            continue
                        ie, id_, filename = line.split(maxsplit=2)
                        self._ydl.archive.add(f"{ie} {id_}")
                        self._all_files[f"{ie} {id_}"] = Path(filename)
            except OSError as ioe:
                if ioe.errno != errno.ENOENT:
                    raise

            old_match_entry = self._ydl._match_entry

            def _match_entry(ydl, info_dict, incomplete=False, silent=False):
                self._downloaded.add(ydl._make_archive_id(info_dict))
                return old_match_entry(info_dict, incomplete, silent)

            self._ydl._match_entry = functools.partial(_match_entry, self._ydl)

        def post_download(self):
            if not self._enabled:
                return
            if getattr(self._ydl, "_abort_event", None) and self._ydl._abort_event.is_set():
                return
            to_remove = {self._all_files[key] for key in (set(self._all_files.keys()) - self._downloaded)}
            self._ydl._delete_downloaded_files(*to_remove)
            with locked_file(self._sync_file, "w", encoding="utf-8") as archive_file:
                for k, v in self._all_files.items():
                    if k in self._downloaded:
                        archive_file.write(f"{k} {v}\n")

    # 7. CLI Option Parser Adapter
    def _parse_patched_options(opts):
        patched_parser = ytdl_options.create_parser()
        patched_parser.defaults.update({
            "ignoreerrors": False,
            "retries": 0,
            "fragment_retries": 0,
            "extract_flat": False,
            "concat_playlist": "never",
        })
        ytdl_options.create_parser = lambda: patched_parser
        try:
            return yt_dlp.parse_options(opts)
        finally:
            ytdl_options.create_parser = _create_parser_patched

    _default_opts = _parse_patched_options([]).ydl_opts

    def cli_to_api(opts):
        opts = yt_dlp.parse_options(opts).ydl_opts
        diff = {k: v for k, v in opts.items() if _default_opts.get(k) != v}
        if "postprocessors" in diff:
            diff["postprocessors"] = [pp for pp in diff["postprocessors"] if pp not in _default_opts.get("postprocessors", [])]
        return diff


# 8. MutagenPP (ID3, Vorbis, FLAC, MP4 tagging)
if YTDLP_AVAILABLE and MUTAGEN_AVAILABLE:
    class MutagenPostProcessorError(PostProcessingError):
        pass

    class MutagenPP(PostProcessor):
        _MUTAGEN_SUPPORTED_EXTS = ("alac", "aiff", "flac", "mp3", "m4a", "ogg", "opus", "vorbis", "wav")
        _VORBIS_METADATA: ClassVar[dict[str, str]] = {
            "title": "title", "artist": "artist", "genre": "genre", "album": "album",
            "albumartist": "album_artist", "comment": "description", "composer": "composer",
            "tracknumber": "track", "WWWAUDIOFILE": "purl",
        }
        _ID3_METADATA: ClassVar[dict[str, str]] = {
            "TIT2": "title", "TPE1": "artist", "COMM": "description", "TCON": "genre",
            "WOAF": "purl", "TALB": "album", "TPE2": "album_artist", "TRCK": "track",
            "TCOM": "composer", "TPOS": "disc",
        }
        _MP4_METADATA: ClassVar[dict[str, str]] = {
            "\251ART": "artist", "\251nam": "title", "\251gen": "genre", "\251alb": "album",
            "aART": "album_artist", "\251cmt": "description", "\251wrt": "composer",
            "disk": "disc", "tvsh": "show", "tvsn": "season_number", "egid": "episode_id",
            "tven": "episode_sort",
        }

        def __init__(self, post_overwrites: bool, downloader=None):
            super().__init__(downloader)
            self._post_overwrites = post_overwrites

        def _get_flac_pic(self, thumbnail: dict) -> flac.Picture:
            pic = flac.Picture()
            pic.data = thumbnail["data"]
            pic.mime = f"image/{thumbnail['type']}"
            pic.type = id3.PictureType.COVER_FRONT
            return pic

        def _get_metadata_dict(self, info):
            meta_prefix = "meta"
            metadata = collections.defaultdict(dict)

            def add(meta_list, info_list=None):
                value = next(
                    (
                        info[key]
                        for key in [f"{meta_prefix}_", *variadic(info_list or meta_list)]
                        if info.get(key) is not None
                    ),
                    None,
                )
                if value not in ("", None):
                    value = ", ".join(map(str, variadic(value)))
                    value = value.replace("\0", "")
                    metadata["common"].update({meta_f: value for meta_f in variadic(meta_list)})

            add("title", ("track", "title"))
            add("date", "upload_date")
            add(("description", "synopsis"), "description")
            add(("purl", "comment"), "webpage_url")
            add("track", "track_number")
            add("artist", ("artist", "artists", "creator", "creators", "uploader", "uploader_id"))
            add("composer", ("composer", "composers"))
            add("genre", ("genre", "genres"))
            add("album")
            add("album_artist", ("album_artist", "album_artists"))
            add("disc", "disc_number")
            add("show", "series")
            add("season_number")
            add("episode_id", ("episode", "episode_id"))
            add("episode_sort", "episode_number")
            if "embed-metadata" in self.get_param("compat_opts", []):
                add("comment", "description")
                metadata["common"].pop("synopsis", None)

            meta_regex = rf"{re.escape(meta_prefix)}(?P<i>\d+)?_(?P<key>.+)"
            for key, value in info.items():
                mobj = re.fullmatch(meta_regex, key)
                if value is not None and mobj:
                    metadata[mobj.group("i") or "common"][mobj.group("key")] = value.replace("\0", "")
            return metadata

        @functools.singledispatchmethod
        def _assemble_metadata(self, file: FileType, meta: dict) -> None:
            raise MutagenPostProcessorError(f"Filetype {file.__class__.__name__} is not currently supported")

        @_assemble_metadata.register(flac.FLAC)
        def _(self, file: flac.FLAC, meta: dict) -> None:
            for file_key, meta_key in self._VORBIS_METADATA.items():
                if meta.get(meta_key):
                    file[file_key] = meta[meta_key]
            if meta.get("date"):
                date = date_from_str(meta["date"])
                file["date"] = date.strftime("%Y-%m-%d")
            if meta.get("thumbnail"):
                pic = self._get_flac_pic(meta["thumbnail"])
                file.add_picture(pic)

        @_assemble_metadata.register(oggvorbis.OggVorbis)
        @_assemble_metadata.register(oggtheora.OggTheora)
        @_assemble_metadata.register(oggspeex.OggSpeex)
        @_assemble_metadata.register(oggopus.OggOpus)
        def _(self, file: oggopus.OggOpus, meta: dict) -> None:
            for file_key, meta_key in self._VORBIS_METADATA.items():
                if meta.get(meta_key):
                    file[file_key] = meta[meta_key]
            if meta.get("date"):
                date = date_from_str(meta["date"])
                file["date"] = date.strftime("%Y-%m-%d")
            if meta.get("thumbnail"):
                pic = self._get_flac_pic(meta["thumbnail"])
                file["METADATA_BLOCK_PICTURE"] = base64.b64encode(pic.write()).decode("ascii")

        @_assemble_metadata.register(trueaudio.TrueAudio)
        @_assemble_metadata.register(dsf.DSF)
        @_assemble_metadata.register(dsdiff.DSDIFF)
        @_assemble_metadata.register(aiff.AIFF)
        @_assemble_metadata.register(mp3.MP3)
        @_assemble_metadata.register(wave.WAVE)
        def _(self, file: wave.WAVE, meta: dict) -> None:
            for file_key, meta_key in self._ID3_METADATA.items():
                if meta.get(meta_key):
                    id3_class = getattr(id3, file_key)
                    if issubclass(id3_class, id3.UrlFrame):
                        file[file_key] = id3_class(url=meta[meta_key])
                    else:
                        file[file_key] = id3_class(encoding=id3.Encoding.UTF8, text=meta[meta_key])
            if meta.get("date"):
                date = date_from_str(meta["date"])
                file["TDRC"] = id3.TDRC(encoding=id3.Encoding.UTF8, text=date.strftime("%Y-%m-%d"))
            if meta.get("thumbnail"):
                file["APIC"] = id3.APIC(
                    encoding=3,
                    mime=f'image/{meta["thumbnail"]["type"]}',
                    type=3,
                    desc="Cover (front)",
                    data=meta["thumbnail"]["data"],
                )

        @_assemble_metadata.register(mp4.MP4)
        def _(self, file: mp4.MP4, meta: dict) -> None:
            for file_key, meta_key in self._MP4_METADATA.items():
                if meta.get(meta_key):
                    file[file_key] = meta[meta_key]
            if meta.get("date"):
                date = date_from_str(meta["date"])
                file["\251day"] = date.strftime("%Y-%m-%d")
            if meta.get("purl"):
                file["----:com.apple.iTunes:WWWAUDIOFILE"] = meta["purl"].encode()
                file["purl"] = meta["purl"]
            if meta.get("track"):
                with contextlib.suppress(ValueError):
                    file["trkn"] = [(int(meta["track"]), 0)]
            if meta.get("thumbnail"):
                f = {"jpeg": mp4.MP4Cover.FORMAT_JPEG, "png": mp4.MP4Cover.FORMAT_PNG}
                file["covr"] = [mp4.MP4Cover(meta["thumbnail"]["data"], f[meta["thumbnail"]["type"]])]

        def _get_thumbnail(self, info: dict):
            if not info.get("thumbnails"):
                return None
            idx = next((-i for i, t in enumerate(info["thumbnails"][::-1], 1) if t.get("filepath")), None)
            if idx is None:
                return None
            thumbnail_filename = info["thumbnails"][idx]["filepath"]
            if not os.path.exists(thumbnail_filename):
                return None
            with open(thumbnail_filename, "rb") as thumbfile:
                thumb_data = thumbfile.read()
            self._delete_downloaded_files(thumbnail_filename, info=info)
            type_ = imghdr.what(h=thumb_data)
            if not type_ or type_ not in {"jpeg", "png"}:
                return None
            return {"data": thumb_data, "type": type_}

        def run(self, info: dict):
            if getattr(self._downloader, "_abort_event", None) and self._downloader._abort_event.is_set():
                raise AbortDownloadException("Người dùng đã hủy quá trình tải.")
            thumbnail = self._get_thumbnail(info)
            if not info.get("__real_download") and not self._post_overwrites:
                return [], info
            filename = info["filepath"]
            metadata = self._get_metadata_dict(info)["common"]
            if thumbnail:
                metadata["thumbnail"] = thumbnail
            if not metadata:
                return [], info
            if info["ext"] not in self._MUTAGEN_SUPPORTED_EXTS:
                raise MutagenPostProcessorError(f'Unsupported file extension: {info["ext"]}')
            try:
                f = mutagen.File(filename)
                if f is not None:
                    self._assemble_metadata(f, metadata)
                    f.save()
            except Exception as err:
                raise MutagenPostProcessorError("Unable to embed metadata") from err
            return [], info


# ==============================================================================
# PHẦN 2: LỚP ĐIỀU PHỐI ĐỘNG CƠ TẢI (CORE DOWNLOAD ENGINE)
# ==============================================================================

class GUIYTLogger:
    """Chuyển hướng log từ yt-dlp trực tiếp vào giao diện GUI."""
    def __init__(self, log_cb, debug_mode=False, hide_warnings=False, abort_event=None):
        self.log_cb = log_cb
        self.debug_mode = debug_mode
        self.hide_warnings = hide_warnings
        self.abort_event = abort_event

    def debug(self, msg: object):
        if self.abort_event and self.abort_event.is_set():
            return
        msg_str = str(msg)
        if msg_str.startswith("[debug] "):
            if self.debug_mode:
                self.log_cb(msg_str)
        else:
            self.info(msg_str)

    def info(self, msg: object):
        if self.abort_event and self.abort_event.is_set():
            return
        self.log_cb(str(msg))

    def warning(self, msg: object):
        if self.abort_event and self.abort_event.is_set():
            return
        if not self.hide_warnings:
            self.log_cb(f"⚠️ {msg}")

    def error(self, msg: object):
        if self.abort_event and self.abort_event.is_set():
            return
        msg_str = str(msg)
        if "AbortDownloadException" in msg_str or "DownloadCancelled" in msg_str or "Người dùng đã hủy" in msg_str:
            return
        self.log_cb(f"❌ {msg}")


def convert_v2_name_format(s: str) -> str:
    replacements = {
        "{id}": "%(id)s",
        "{user[username]}": "%(uploader)s",
        "{user[id]}": "%(uploader_id)s",
        "{user[permalink_url]}": "%(uploader_url)s",
        "{timestamp}": "%(timestamp)s",
        "{title}": "%(title)s",
        "{description}": "%(description)s",
        "{duration}": "%(duration)s",
        "{permalink_url}": "%(webpage_url)s",
        "{license}": "%(license)s",
        "{playback_count}": "%(view_count)s",
        "{likes_count}": "%(like_count)s",
        "{comment_count}": "%(comment_count)s",
        "{reposts_count}": "%(respost_count)s",
        "{playlist[author]}": "%(playlist_uploader)s",
        "{playlist[title]}": "%(playlist)s",
        "{playlist[id]}": "%(playlist_id)s",
        "{playlist[tracknumber]}": "%(playlist_index)s",
        "{playlist[tracknumber_total]}": "%(playlist_count)s",
    }
    for old, new in replacements.items():
        s = s.replace(old, new)
    if not s.endswith(".%(ext)s"):
        s += ".%(ext)s"
    return s


def build_ytdl_output_filename(scdl_args: dict, in_playlist: bool, force_suffix: Optional[str] = None) -> str:
    if scdl_args.get("name_format") == "-":
        return "-"

    playlist_format = "%(playlist|)s"
    if in_playlist:
        track_format = convert_v2_name_format(scdl_args.get("playlist_name_format") or "{playlist[tracknumber]} - {title}")
    else:
        track_format = convert_v2_name_format(scdl_args.get("name_format") or "{user[username]} - {title}")

    if scdl_args.get("addtimestamp") or scdl_args.get("addtofile"):
        track_format = "%(title)s.%(ext)s"
        if scdl_args.get("addtofile"):
            track_format = "%(uploader)s - " + track_format
        if scdl_args.get("addtimestamp"):
            track_format = "%(timestamp)s_" + track_format

    base = Path(scdl_args.get("path") or ".").resolve()
    if scdl_args.get("no_playlist_folder") or not in_playlist:
        ret = base / track_format
    else:
        ret = base / playlist_format / track_format

    if force_suffix:
        ret = ret.with_suffix(force_suffix)

    return ret.as_posix()


def build_ytdl_format_specifier(scdl_args: dict) -> str:
    fmt = "ba"
    if scdl_args.get("min_size"):
        fmt += f"[filesize_approx>={scdl_args['min_size']}]"
    if scdl_args.get("max_size"):
        fmt += f"[filesize_approx<={scdl_args['max_size']}]"
    if scdl_args.get("no_original"):
        fmt += "[format_id!=download]"
    if scdl_args.get("only_original"):
        fmt += "[format_id=download]"
    if scdl_args.get("onlymp3"):
        fmt += "[format_id*=mp3]"
    return fmt


def search_soundcloud_url(client: SoundCloud, query: str, log_fn=None, abort_event=None) -> Optional[str]:
    if abort_event and abort_event.is_set():
        return None
    try:
        results = list(client.search(query, limit=1))
        if abort_event and abort_event.is_set():
            return None
        if results:
            item = results[0]
            if hasattr(item, "permalink_url"):
                if log_fn: log_fn(f"🔎 Tìm thấy kết quả: {item.permalink_url}")
                return item.permalink_url
        if log_fn: log_fn(f"❌ Không tìm thấy kết quả nào cho từ khóa: {query}")
        return None
    except Exception as e:
        if abort_event and abort_event.is_set():
            return None
        if log_fn: log_fn(f"❌ Lỗi tìm kiếm SoundCloud: {e}")
        return None


def build_engine_params(url: str, scdl_args: dict):
    if scdl_args.get("a"):
        pass
    elif scdl_args.get("t"):
        url = posixpath.join(url, "tracks")
    elif scdl_args.get("f"):
        url = posixpath.join(url, "likes")
    elif scdl_args.get("C"):
        url = posixpath.join(url, "comments")
    elif scdl_args.get("p"):
        url = posixpath.join(url, "sets")
    elif scdl_args.get("r"):
        url = posixpath.join(url, "reposts")

    params: dict = {}
    params["--embed-metadata"] = True
    params["--embed-thumbnail"] = True
    params["--remux-video"] = "aac>m4a"
    params["--extractor-args"] = "soundcloud:formats=*_aac,*_mp3"
    params["--use-extractors"] = "soundcloud.*"
    params["--output-na-placeholder"] = ""
    params["--parse-metadata"] = []
    params["--trim-filenames"] = "240b"

    postprocessors = [
        (
            OuttmplPP(
                build_ytdl_output_filename(scdl_args, False),
                build_ytdl_output_filename(scdl_args, True),
            ),
            "pre_process",
        )
    ]

    if scdl_args.get("strict_playlist"):
        params["--abort-on-error"] = True

    if not scdl_args.get("c") and not scdl_args.get("download_archive") and not scdl_args.get("sync"):
        params["--break-on-existing"] = True

    # Vị trí bắt đầu / Phân đoạn tải (-o / Offset / Range)
    offset = scdl_args.get("o")
    if offset:
        offset_str = str(offset).strip()
        if offset_str.isdigit():
            params["--playlist-items"] = f"{offset_str}:"
        else:
            params["--playlist-items"] = offset_str

    if scdl_args.get("extract_artist"):
        params["--parse-metadata"] += [
            r"%(title)s:(?P<meta_artist>.*?)\s+[-−–—―]\s*(?P<meta_title>.*)",
        ]

    if scdl_args.get("debug"):
        params["--verbose"] = True
    if scdl_args.get("error"):
        params["--quiet"] = True

    if scdl_args.get("download_archive"):
        params["--download-archive"] = scdl_args.get("download_archive")

    if scdl_args.get("hide_progress"):
        params["--no-progress"] = True

    if scdl_args.get("max_size"):
        params["--max-filesize"] = scdl_args.get("max_size")
    if scdl_args.get("min_size"):
        params["--min-filesize"] = scdl_args.get("min_size")

    params["-f"] = build_ytdl_format_specifier(scdl_args)

    if scdl_args.get("flac"):
        params["--recode-video"] = "aiff>flac/alac>flac/wav>flac"

    if not scdl_args.get("no_album_tag"):
        params["--parse-metadata"] += [
            "%(playlist)s:%(meta_album)s",
            "%(playlist_uploader)s:%(meta_album_artist)s",
            "%(playlist_index)s:%(meta_track)s",
        ]

    if scdl_args.get("original_name") and not scdl_args.get("no_original"):
        postprocessors.append((OriginalFilenamePP(), "pre_process"))

    if not scdl_args.get("original_art"):
        params["--thumbnail-id"] = "t500x500"

    if scdl_args.get("name_format") == "-":
        params["--embed-metadata"] = False
        params["--embed-thumbnail"] = False

    if scdl_args.get("original_metadata") or not MUTAGEN_AVAILABLE:
        params["--embed-metadata"] = False
        params["--embed-thumbnail"] = False
    else:
        postprocessors.append((MutagenPP(scdl_args.get("force_metadata", False)), "post_process"))

    if scdl_args.get("auth_token"):
        params["--username"] = "oauth"
        params["--password"] = scdl_args.get("auth_token")

    if scdl_args.get("overwrite"):
        params["--force-overwrites"] = True

    if scdl_args.get("no_playlist"):
        params["--match-filters"] = "!playlist_uploader"

    if scdl_args.get("add_description"):
        params["--print-to-file"] = (
            "description",
            build_ytdl_output_filename(scdl_args, False, ".txt"),
        )

    if scdl_args.get("opus"):
        params["--extractor-args"] = "soundcloud:formats=*_aac,*_opus,*_mp3"

    argv = []
    for param, value in params.items():
        if value is False:
            continue
        if value is True:
            argv.append(param)
        elif isinstance(value, list):
            for v in value:
                argv.append(param)
                argv.append(v)
        elif isinstance(value, tuple):
            argv.append(param)
            argv += list(value)
        else:
            argv.append(param)
            argv.append(value)

    return url, cli_to_api(argv), postprocessors


# ==============================================================================
# PHẦN 3: GIAO DIỆN NGƯỜI DÙNG HIỆN ĐẠI (MODERN TKINTER GUI)
# ==============================================================================

class ModernSCDLApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("SoundCloud Downloader Pro - Độc Lập & Tối Ưu")
        self.root.geometry("900x740")
        self.root.minsize(800, 640)

        # Luôn mở toàn màn hình (Maximized Full Screen)
        try:
            if sys.platform == "win32":
                self.root.state("zoomed")
            else:
                self.root.attributes("-zoomed", True)
        except Exception:
            pass

        # Cờ hủy tiến trình và quản lý luồng
        self.abort_event = threading.Event()
        self.is_downloading = False

        # Hàng đợi đồng bộ giao diện an toàn đa luồng (Thread-safe UI Dispatcher)
        self.ui_queue = queue.Queue()
        self._poll_ui_queue()

        # Xác định tệp cấu hình setting trong cùng thư mục với script
        self.settings_file = self._get_settings_path()

        # Thư mục tải mặc định thông minh
        default_music_dir = Path.home() / "Music" / "SoundCloud"
        try:
            default_music_dir.mkdir(parents=True, exist_ok=True)
        except Exception:
            default_music_dir = Path(".").resolve()
        self.default_save_path = str(default_music_dir)

        # Cấu hình giao diện và màu sắc Modern Dark
        self._setup_styles()
        self._init_variables()
        self._load_settings()  # Nạp hoặc tự động tạo tệp setting
        self._bind_auto_save_traces()  # Lắng nghe thay đổi realtime trên mọi tùy chọn
        self._build_ui()

        # Bắt sự kiện đóng ứng dụng để tự động lưu setting
        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)

        # Kiểm tra dependencies
        if MISSING_DEPS:
            self.root.after(200, self._warn_missing_deps)

    def _post_ui(self, fn, *args):
        """Đẩy lệnh cập nhật giao diện vào hàng đợi thread-safe để thực thi trên luồng chính."""
        self.ui_queue.put((fn, args))

    def _poll_ui_queue(self):
        """Bộ quét hàng đợi định kỳ trên luồng chính Tkinter, giải quyết triệt để lỗi luồng."""
        try:
            while not self.ui_queue.empty():
                fn, args = self.ui_queue.get_nowait()
                try:
                    fn(*args)
                except Exception:
                    pass
        finally:
            try:
                self.root.after(30, self._poll_ui_queue)
            except Exception:
                pass

    def _warn_missing_deps(self):
        deps_str = ", ".join(MISSING_DEPS)
        messagebox.showwarning(
            "Cảnh báo thiếu thư viện",
            f"Một số thư viện cần thiết chưa được cài đặt: {deps_str}\n\n"
            f"Vui lòng mở terminal và chạy lệnh:\n"
            f"pip install {' '.join(MISSING_DEPS)}"
        )

    def _setup_styles(self):
        self.colors = {
            "bg": "#1e1e24",
            "card": "#282833",
            "card_sub": "#22222c",
            "primary": "#ff5500",      # SoundCloud Orange
            "primary_hover": "#ff6a1a",
            "danger": "#e74c3c",       # Abort Red
            "danger_hover": "#c0392b",
            "success": "#2ecc71",
            "text": "#ffffff",
            "text_muted": "#a6adc8",
            "entry_bg": "#181820",
            "console_bg": "#111116",
            "console_fg": "#50fa7b",
        }

        self.root.configure(bg=self.colors["bg"])
        self.style = ttk.Style()
        self.style.theme_use("clam")

        self.style.configure(".", background=self.colors["bg"], foreground=self.colors["text"], font=("Segoe UI", 9))
        self.style.configure("TFrame", background=self.colors["bg"])
        self.style.configure("Card.TFrame", background=self.colors["card"])
        self.style.configure("TLabel", background=self.colors["bg"], foreground=self.colors["text"])
        self.style.configure("Card.TLabel", background=self.colors["card"], foreground=self.colors["text"])
        self.style.configure("Muted.TLabel", background=self.colors["card"], foreground=self.colors["text_muted"], font=("Segoe UI", 8))

        # Buttons
        self.style.configure("Primary.TButton", font=("Segoe UI", 10, "bold"), background=self.colors["primary"], foreground="#ffffff", borderwidth=0)
        self.style.map("Primary.TButton", background=[("active", self.colors["primary_hover"]), ("disabled", "#555555")])

        self.style.configure("Danger.TButton", font=("Segoe UI", 9, "bold"), background=self.colors["danger"], foreground="#ffffff", borderwidth=0)
        self.style.map("Danger.TButton", background=[("active", self.colors["danger_hover"]), ("disabled", "#555555")])

        self.style.configure("Outline.TButton", font=("Segoe UI", 9), background=self.colors["card_sub"], foreground="#ffffff")
        self.style.map("Outline.TButton", background=[("active", "#3a3a4c")])

        # Notebook (Tabs)
        self.style.configure("TNotebook", background=self.colors["bg"], tabmargins=[2, 5, 2, 0])
        self.style.configure("TNotebook.Tab", background=self.colors["card_sub"], foreground=self.colors["text_muted"], padding=[14, 6], font=("Segoe UI", 9, "bold"))
        self.style.map("TNotebook.Tab",
            background=[("selected", self.colors["primary"]), ("active", "#333344")],
            foreground=[("selected", "#ffffff"), ("active", "#ffffff")]
        )

        # Checkbutton / Radiobutton
        self.style.configure("TCheckbutton", background=self.colors["card"], foreground=self.colors["text"])
        self.style.map("TCheckbutton", background=[("active", self.colors["card"])])
        self.style.configure("TRadiobutton", background=self.colors["card"], foreground=self.colors["text"])
        self.style.map("TRadiobutton", background=[("active", self.colors["card"])])

        # Progressbar
        self.style.configure("TProgressbar", thickness=10, background=self.colors["primary"], troughcolor=self.colors["console_bg"])

        # LabelFrames
        self.style.configure("TLabelframe", background=self.colors["card"], foreground=self.colors["primary"])
        self.style.configure("TLabelframe.Label", background=self.colors["card"], foreground=self.colors["primary"], font=("Segoe UI", 9, "bold"))

    def _init_variables(self):
        # Tab 1: Cơ bản
        self.var_url = tk.StringVar()
        self.var_is_search = tk.BooleanVar(value=False)
        self.var_mode = tk.StringVar(value="-l")
        self.var_offset = tk.StringVar()  # Offset / Dải bài (Tính năng trọng tâm)
        self.var_path = tk.StringVar(value=self.default_save_path)

        # Tab 2: Định dạng & Giới hạn
        self.var_onlymp3 = tk.BooleanVar(value=False)
        self.var_flac = tk.BooleanVar(value=False)
        self.var_opus = tk.BooleanVar(value=False)
        self.var_original_choice = tk.StringVar(value="default")  # default, only, none
        self.var_min_size = tk.StringVar()
        self.var_max_size = tk.StringVar()

        # Tab 3: Metadata & Tên file
        self.var_force_meta = tk.BooleanVar(value=False)
        self.var_orig_meta = tk.BooleanVar(value=False)
        self.var_extract_artist = tk.BooleanVar(value=True)  # Mặc định nên bật để tách ca sĩ sạch đẹp
        self.var_no_album_tag = tk.BooleanVar(value=False)
        self.var_orig_art = tk.BooleanVar(value=True)        # Mặc định lấy ảnh bìa nét nhất
        self.var_orig_name = tk.BooleanVar(value=False)
        self.var_add_desc = tk.BooleanVar(value=False)
        self.var_name_format = tk.StringVar(value="{user[username]} - {title}")
        self.var_pl_name_format = tk.StringVar(value="{playlist[tracknumber]} - {title}")

        # Tab 4: Nâng cao & Xác thực
        self.var_continue = tk.BooleanVar(value=True)
        self.var_overwrite = tk.BooleanVar(value=False)
        self.var_no_pl_folder = tk.BooleanVar(value=False)
        self.var_no_playlist = tk.BooleanVar(value=False)
        self.var_strict_pl = tk.BooleanVar(value=False)
        self.var_concurrent_fragments = tk.StringVar(value="4")  # Đa luồng tải phân đoạn audio
        self.var_auth_token = tk.StringVar()
        self.var_client_id = tk.StringVar()
        self.var_archive = tk.StringVar()
        self.var_sync = tk.StringVar()
        self.var_ytdlp_args = tk.StringVar()
        self.var_debug = tk.BooleanVar(value=False)
        self.var_hidewarnings = tk.BooleanVar(value=False)

        # Nhật ký & Tiến trình
        self.var_status = tk.StringVar(value="Sẵn sàng thực thi")
        self.var_progress_track = tk.StringVar(value="Chưa có tác vụ")
        self.var_progress_metrics = tk.StringVar(value="Tốc độ: -- | ETA: -- | Tiến độ: 0%")
        self.var_autoscroll = tk.BooleanVar(value=True)

        self._save_timer = None
        self._is_loading_settings = False

    def _get_settings_path(self) -> Path:
        try:
            if getattr(sys, "frozen", False):
                base_dir = Path(sys.executable).resolve().parent
            else:
                base_dir = Path(__file__).resolve().parent
        except Exception:
            base_dir = Path(".").resolve()
        return base_dir / "scld_settings.json"

    def _load_settings(self):
        self._is_loading_settings = True
        try:
            if not self.settings_file.exists():
                # Tự động tạo tệp setting mặc định ban đầu trong cùng thư mục
                self._save_settings()
                return

            with open(self.settings_file, "r", encoding="utf-8") as f:
                data = json.load(f)

            if "path" in data and data["path"]:
                self.var_path.set(data["path"])
            if "mode" in data:
                self.var_mode.set(data["mode"])
            if "is_search" in data:
                self.var_is_search.set(bool(data["is_search"]))
            if "offset" in data:
                self.var_offset.set(str(data["offset"]))
            if "onlymp3" in data:
                self.var_onlymp3.set(bool(data["onlymp3"]))
            if "flac" in data:
                self.var_flac.set(bool(data["flac"]))
            if "opus" in data:
                self.var_opus.set(bool(data["opus"]))
            if "original_choice" in data:
                self.var_original_choice.set(str(data["original_choice"]))
            if "min_size" in data:
                self.var_min_size.set(str(data["min_size"]))
            if "max_size" in data:
                self.var_max_size.set(str(data["max_size"]))
            if "force_metadata" in data:
                self.var_force_meta.set(bool(data["force_metadata"]))
            if "original_metadata" in data:
                self.var_orig_meta.set(bool(data["original_metadata"]))
            if "extract_artist" in data:
                self.var_extract_artist.set(bool(data["extract_artist"]))
            if "no_album_tag" in data:
                self.var_no_album_tag.set(bool(data["no_album_tag"]))
            if "original_art" in data:
                self.var_orig_art.set(bool(data["original_art"]))
            if "original_name" in data:
                self.var_orig_name.set(bool(data["original_name"]))
            if "add_description" in data:
                self.var_add_desc.set(bool(data["add_description"]))
            if "name_format" in data and data["name_format"]:
                self.var_name_format.set(str(data["name_format"]))
            if "playlist_name_format" in data and data["playlist_name_format"]:
                self.var_pl_name_format.set(str(data["playlist_name_format"]))
            if "continue" in data:
                self.var_continue.set(bool(data["continue"]))
            if "overwrite" in data:
                self.var_overwrite.set(bool(data["overwrite"]))
            if "no_playlist_folder" in data:
                self.var_no_pl_folder.set(bool(data["no_playlist_folder"]))
            if "no_playlist" in data:
                self.var_no_playlist.set(bool(data["no_playlist"]))
            if "strict_playlist" in data:
                self.var_strict_pl.set(bool(data["strict_playlist"]))
            if "concurrent_fragments" in data:
                self.var_concurrent_fragments.set(str(data["concurrent_fragments"]))
            if "auth_token" in data:
                self.var_auth_token.set(str(data["auth_token"]))
            if "client_id" in data:
                self.var_client_id.set(str(data["client_id"]))
            if "download_archive" in data:
                self.var_archive.set(str(data["download_archive"]))
            if "sync" in data:
                self.var_sync.set(str(data["sync"]))
            if "yt_dlp_args" in data:
                self.var_ytdlp_args.set(str(data["yt_dlp_args"]))
            if "debug" in data:
                self.var_debug.set(bool(data["debug"]))
            if "hidewarnings" in data:
                self.var_hidewarnings.set(bool(data["hidewarnings"]))
            if "autoscroll" in data:
                self.var_autoscroll.set(bool(data["autoscroll"]))
        except Exception:
            pass
        finally:
            self._is_loading_settings = False

    def _schedule_auto_save(self, *args):
        if getattr(self, "_is_loading_settings", False):
            return
        if hasattr(self, "_save_timer") and self._save_timer:
            try:
                self.root.after_cancel(self._save_timer)
            except Exception:
                pass
        # Debounce 100ms: ghi nhận ngay lập tức khi người dùng nhấn/chọn hoặc vừa nhập xong
        self._save_timer = self.root.after(100, self._save_settings)

    def _bind_auto_save_traces(self):
        tracked_vars = [
            self.var_path, self.var_mode, self.var_is_search, self.var_offset,
            self.var_onlymp3, self.var_flac, self.var_opus, self.var_original_choice,
            self.var_min_size, self.var_max_size, self.var_force_meta, self.var_orig_meta,
            self.var_extract_artist, self.var_no_album_tag, self.var_orig_art,
            self.var_orig_name, self.var_add_desc, self.var_name_format,
            self.var_pl_name_format, self.var_continue, self.var_overwrite,
            self.var_no_pl_folder, self.var_no_playlist, self.var_strict_pl,
            self.var_concurrent_fragments, self.var_auth_token, self.var_client_id,
            self.var_archive, self.var_sync, self.var_ytdlp_args, self.var_debug,
            self.var_hidewarnings, self.var_autoscroll,
        ]
        for v in tracked_vars:
            v.trace_add("write", self._schedule_auto_save)

    def _save_settings(self):
        data = {
            "path": self.var_path.get(),
            "mode": self.var_mode.get(),
            "is_search": self.var_is_search.get(),
            "offset": self.var_offset.get(),
            "onlymp3": self.var_onlymp3.get(),
            "flac": self.var_flac.get(),
            "opus": self.var_opus.get(),
            "original_choice": self.var_original_choice.get(),
            "min_size": self.var_min_size.get(),
            "max_size": self.var_max_size.get(),
            "force_metadata": self.var_force_meta.get(),
            "original_metadata": self.var_orig_meta.get(),
            "extract_artist": self.var_extract_artist.get(),
            "no_album_tag": self.var_no_album_tag.get(),
            "original_art": self.var_orig_art.get(),
            "original_name": self.var_orig_name.get(),
            "add_description": self.var_add_desc.get(),
            "name_format": self.var_name_format.get(),
            "playlist_name_format": self.var_pl_name_format.get(),
            "continue": self.var_continue.get(),
            "overwrite": self.var_overwrite.get(),
            "no_playlist_folder": self.var_no_pl_folder.get(),
            "no_playlist": self.var_no_playlist.get(),
            "strict_playlist": self.var_strict_pl.get(),
            "concurrent_fragments": self.var_concurrent_fragments.get(),
            "auth_token": self.var_auth_token.get(),
            "client_id": self.var_client_id.get(),
            "download_archive": self.var_archive.get(),
            "sync": self.var_sync.get(),
            "yt_dlp_args": self.var_ytdlp_args.get(),
            "debug": self.var_debug.get(),
            "hidewarnings": self.var_hidewarnings.get(),
            "autoscroll": self.var_autoscroll.get(),
        }
        try:
            with open(self.settings_file, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)
        except Exception:
            pass

    def _on_closing(self):
        self._save_settings()
        self.root.destroy()

    def _build_ui(self):
        # 1. Header Banner
        header = ttk.Frame(self.root, padding="15 10")
        header.pack(fill=tk.X)

        title_lbl = tk.Label(header, text="☁ SoundCloud Downloader Pro", font=("Segoe UI", 14, "bold"), fg=self.colors["primary"], bg=self.colors["bg"])
        title_lbl.pack(side=tk.LEFT)

        subtitle_lbl = tk.Label(header, text="Monolithic Engine | Đa luồng | Độc lập", font=("Segoe UI", 9), fg=self.colors["text_muted"], bg=self.colors["bg"])
        subtitle_lbl.pack(side=tk.LEFT, padx=15, pady=3)

        self.lbl_badge = tk.Label(header, textvariable=self.var_status, font=("Segoe UI", 9, "bold"), fg="#ffffff", bg="#3a3a4c", padx=10, pady=3)
        self.lbl_badge.pack(side=tk.RIGHT)

        # 2. Main Tabbed Notebook
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=False, padx=12, pady=4)

        self._build_tab_basic()
        self._build_tab_format()
        self._build_tab_metadata()
        self._build_tab_advanced()

        # 3. Dashboard Tiến Trình (Real-time Progress Dashboard)
        dash_frame = tk.LabelFrame(self.root, text=" 📊 Tiến Độ Thời Gian Thực ", bg=self.colors["card"], fg=self.colors["primary"], font=("Segoe UI", 9, "bold"), padx=10, pady=6)
        dash_frame.pack(fill=tk.X, padx=12, pady=6)

        lbl_track = tk.Label(dash_frame, textvariable=self.var_progress_track, font=("Segoe UI", 9, "bold"), anchor="w", bg=self.colors["card"], fg="#ffffff")
        lbl_track.pack(fill=tk.X)

        lbl_metrics = tk.Label(dash_frame, textvariable=self.var_progress_metrics, font=("Consolas", 8), anchor="w", bg=self.colors["card"], fg=self.colors["text_muted"])
        lbl_metrics.pack(fill=tk.X, pady=(2, 4))

        self.progress_bar = ttk.Progressbar(dash_frame, mode="determinate")
        self.progress_bar.pack(fill=tk.X, pady=2)

        # 4. Action Control Bar
        ctl_frame = ttk.Frame(self.root, padding="12 4")
        ctl_frame.pack(fill=tk.X)

        self.btn_download = ttk.Button(ctl_frame, text="🚀 BẮT ĐẦU TẢI", style="Primary.TButton", command=self._start_download)
        self.btn_download.pack(side=tk.RIGHT, padx=4, ipadx=15, ipady=4)

        self.btn_abort = ttk.Button(ctl_frame, text="⏹ HỦY TẢI", style="Danger.TButton", command=self._abort_download, state=tk.DISABLED)
        self.btn_abort.pack(side=tk.RIGHT, padx=4, ipadx=10, ipady=4)

        btn_open_folder = ttk.Button(ctl_frame, text="📁 Mở Thư Mục Lưu", style="Outline.TButton", command=self._open_download_folder)
        btn_open_folder.pack(side=tk.LEFT, padx=4)

        btn_clear_log = ttk.Button(ctl_frame, text="🧹 Xóa Log", style="Outline.TButton", command=self._clear_log)
        btn_clear_log.pack(side=tk.LEFT, padx=4)

        chk_scroll = ttk.Checkbutton(ctl_frame, text="Tự động cuộn", variable=self.var_autoscroll)
        chk_scroll.pack(side=tk.LEFT, padx=8)

        # 5. Console Nhật Ký
        log_container = tk.Frame(self.root, bg=self.colors["console_bg"], bd=1, relief=tk.SOLID)
        log_container.pack(fill=tk.BOTH, expand=True, padx=12, pady=(0, 10))

        self.txt_log = tk.Text(
            log_container,
            bg=self.colors["console_bg"],
            fg=self.colors["console_fg"],
            insertbackground="#ffffff",
            font=("Consolas", 9),
            bd=0,
            padx=8,
            pady=6,
            wrap=tk.WORD
        )
        self.txt_log.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(log_container, orient=tk.VERTICAL, command=self.txt_log.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.txt_log.config(yscrollcommand=scrollbar.set)

    # --------------------------------------------------------------------------
    # TAB 1: CƠ BẢN & NGUỒN TẢI
    # --------------------------------------------------------------------------
    def _build_tab_basic(self):
        tab = ttk.Frame(self.notebook, style="Card.TFrame", padding=12)
        self.notebook.add(tab, text=" 🎵 Cơ Bản & Nguồn Tải ")

        # URL Input
        lbl_url = ttk.Label(tab, text="Đường dẫn SoundCloud (URL) hoặc Từ khóa tìm kiếm:", style="Card.TLabel", font=("Segoe UI", 9, "bold"))
        lbl_url.pack(anchor="w")

        url_row = ttk.Frame(tab, style="Card.TFrame")
        url_row.pack(fill=tk.X, pady=(4, 6))

        entry_url = tk.Entry(url_row, textvariable=self.var_url, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", font=("Segoe UI", 9), bd=1, relief=tk.SOLID)
        entry_url.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=4, padx=(0, 6))

        btn_paste = ttk.Button(url_row, text="Dán", style="Outline.TButton", command=self._paste_clipboard)
        btn_paste.pack(side=tk.LEFT, padx=2)

        btn_clear = ttk.Button(url_row, text="Xóa", style="Outline.TButton", command=lambda: self.var_url.set(""))
        btn_clear.pack(side=tk.LEFT, padx=2)

        chk_search = ttk.Checkbutton(tab, text="Đây là từ khóa tìm kiếm trên SoundCloud (-s)", variable=self.var_is_search)
        chk_search.pack(anchor="w", pady=(0, 8))

        # Chế độ tải & Vị trí bài (Offset)
        mid_row = ttk.Frame(tab, style="Card.TFrame")
        mid_row.pack(fill=tk.X, pady=4)

        # Khung chế độ
        mode_frame = ttk.LabelFrame(mid_row, text=" Chế Độ Tải ", style="TLabelframe", padding=8)
        mode_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 8))

        modes = [
            ("Mặc định (Track hoặc Set/Playlist)", "-l"),
            ("Tất cả bài của User (-a)", "-a"),
            ("Chỉ bài upload của User (-t)", "-t"),
            ("Tất cả lượt thích của User (-f)", "-f"),
            ("Tất cả bình luận của User (-C)", "-C"),
            ("Tất cả Playlists của User (-p)", "-p"),
            ("Tất cả Reposts của User (-r)", "-r"),
            ("Tài khoản của tôi (me)", "me")
        ]
        grid_frame = ttk.Frame(mode_frame, style="Card.TFrame")
        grid_frame.pack(fill=tk.X)
        for i, (text, val) in enumerate(modes):
            r = i // 2
            c = i % 2
            ttk.Radiobutton(grid_frame, text=text, variable=self.var_mode, value=val).grid(row=r, column=c, sticky="w", padx=6, pady=2)

        # Khung Vị trí bắt đầu (Offset) - TÍNH NĂNG ĐẶC BIỆT YÊU CẦU
        offset_frame = ttk.LabelFrame(mid_row, text=" Vị Trí Bắt Đầu / Phân Đoạn (-o) ", style="TLabelframe", padding=8)
        offset_frame.pack(side=tk.RIGHT, fill=tk.BOTH, padx=(0, 0))

        ttk.Label(offset_frame, text="Tải từ bài thứ N hoặc Dải bài:", style="Card.TLabel").pack(anchor="w")
        entry_offset = tk.Entry(offset_frame, textvariable=self.var_offset, width=22, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_offset.pack(anchor="w", pady=4, ipady=2)

        hint_text = "Ví dụ:\n• 15 (tải từ bài 15 đến hết)\n• 10-25 (chỉ tải bài 10 đến 25)\n• 1,3,5 (chỉ tải các bài chỉ định)\n(Bỏ trống = tải từ bài đầu tiên)"
        ttk.Label(offset_frame, text=hint_text, style="Muted.TLabel", justify=tk.LEFT).pack(anchor="w")

        # Thư mục lưu file
        path_frame = ttk.Frame(tab, style="Card.TFrame")
        path_frame.pack(fill=tk.X, pady=(10, 2))

        ttk.Label(path_frame, text="Thư mục lưu trữ (--path):", style="Card.TLabel", font=("Segoe UI", 9, "bold")).pack(anchor="w")

        path_row = ttk.Frame(path_frame, style="Card.TFrame")
        path_row.pack(fill=tk.X, pady=3)

        entry_path = tk.Entry(path_row, textvariable=self.var_path, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_path.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=3, padx=(0, 6))

        btn_browse = ttk.Button(path_row, text="Duyệt...", style="Outline.TButton", command=self._browse_folder)
        btn_browse.pack(side=tk.LEFT)

    # --------------------------------------------------------------------------
    # TAB 2: ĐỊNH DẠNG & GIỚI HẠN
    # --------------------------------------------------------------------------
    def _build_tab_format(self):
        tab = ttk.Frame(self.notebook, style="Card.TFrame", padding=12)
        self.notebook.add(tab, text=" 🎛 Định Dạng & Giới Hạn ")

        col1 = ttk.Frame(tab, style="Card.TFrame")
        col1.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 8))

        col2 = ttk.Frame(tab, style="Card.TFrame")
        col2.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(8, 0))

        # Khung định dạng
        fmt_frame = ttk.LabelFrame(col1, text=" Định Dạng Âm Thanh ", style="TLabelframe", padding=10)
        fmt_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Checkbutton(fmt_frame, text="Chỉ tải MP3 (--onlymp3)", variable=self.var_onlymp3).pack(anchor="w", pady=3)
        ttk.Checkbutton(fmt_frame, text="Ưu tiên tải âm thanh Opus (--opus)", variable=self.var_opus).pack(anchor="w", pady=3)
        ttk.Checkbutton(fmt_frame, text="Chuyển đổi sang FLAC lossless nếu có thể (--flac)", variable=self.var_flac).pack(anchor="w", pady=3)

        # Khung file gốc
        orig_frame = ttk.LabelFrame(col1, text=" Cơ Chế Tải File Gốc (Original File) ", style="TLabelframe", padding=10)
        orig_frame.pack(fill=tk.X)

        ttk.Radiobutton(orig_frame, text="Mặc định (Ưu tiên file gốc nếu có, nếu không lấy stream)", variable=self.var_original_choice, value="default").pack(anchor="w", pady=2)
        ttk.Radiobutton(orig_frame, text="Chỉ tải khi có file gốc upload bởi Artist (--only-original)", variable=self.var_original_choice, value="only").pack(anchor="w", pady=2)
        ttk.Radiobutton(orig_frame, text="Không tải file gốc; chỉ tải stream nén (--no-original)", variable=self.var_original_choice, value="none").pack(anchor="w", pady=2)

        # Khung kích thước
        size_frame = ttk.LabelFrame(col2, text=" Lọc Dung Lượng Tệp ", style="TLabelframe", padding=10)
        size_frame.pack(fill=tk.X)

        ttk.Label(size_frame, text="Dung lượng tối thiểu (--min-size):", style="Card.TLabel").pack(anchor="w")
        entry_min = tk.Entry(size_frame, textvariable=self.var_min_size, width=20, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_min.pack(anchor="w", pady=(2, 6), ipady=2)
        ttk.Label(size_frame, text="Ví dụ: 500k, 1m (bỏ qua file nhỏ hơn)", style="Muted.TLabel").pack(anchor="w")

        ttk.Label(size_frame, text="Dung lượng tối đa (--max-size):", style="Card.TLabel").pack(anchor="w", pady=(8, 0))
        entry_max = tk.Entry(size_frame, textvariable=self.var_max_size, width=20, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_max.pack(anchor="w", pady=(2, 6), ipady=2)
        ttk.Label(size_frame, text="Ví dụ: 50m, 1g (bỏ qua file lớn hơn)", style="Muted.TLabel").pack(anchor="w")

    # --------------------------------------------------------------------------
    # TAB 3: SIÊU DỮ LIỆU & TÊN FILE
    # --------------------------------------------------------------------------
    def _build_tab_metadata(self):
        tab = ttk.Frame(self.notebook, style="Card.TFrame", padding=12)
        self.notebook.add(tab, text=" 🏷 Siêu Dữ Liệu & Tên File ")

        meta_frame = ttk.LabelFrame(tab, text=" Cấu Hình Thẻ Nhạc ID3 & Tài Nguyên ", style="TLabelframe", padding=10)
        meta_frame.pack(fill=tk.X, pady=(0, 10))

        grid = ttk.Frame(meta_frame, style="Card.TFrame")
        grid.pack(fill=tk.X)

        ttk.Checkbutton(grid, text="Tự động tách Nghệ sĩ từ Tiêu đề (--extract-artist)", variable=self.var_extract_artist).grid(row=0, column=0, sticky="w", padx=8, pady=3)
        ttk.Checkbutton(grid, text="Tải ảnh bìa gốc phân giải cao (--original-art)", variable=self.var_orig_art).grid(row=0, column=1, sticky="w", padx=8, pady=3)

        ttk.Checkbutton(grid, text="Ép ghi Metadata cho cả file cũ (--force-metadata)", variable=self.var_force_meta).grid(row=1, column=0, sticky="w", padx=8, pady=3)
        ttk.Checkbutton(grid, text="Giữ nguyên Metadata gốc (--original-metadata)", variable=self.var_orig_meta).grid(row=1, column=1, sticky="w", padx=8, pady=3)

        ttk.Checkbutton(grid, text="Bỏ thẻ Album để tránh lỗi trùng bìa (--no-album-tag)", variable=self.var_no_album_tag).grid(row=2, column=0, sticky="w", padx=8, pady=3)
        ttk.Checkbutton(grid, text="Giữ nguyên tên file tác giả upload (--original-name)", variable=self.var_orig_name).grid(row=2, column=1, sticky="w", padx=8, pady=3)

        ttk.Checkbutton(grid, text="Lưu mô tả bài hát ra file TXT (--add-description)", variable=self.var_add_desc).grid(row=3, column=0, sticky="w", padx=8, pady=3)

        # Naming format
        name_frame = ttk.LabelFrame(tab, text=" Mẫu Đặt Tên Tệp (Name Formatting Templates) ", style="TLabelframe", padding=10)
        name_frame.pack(fill=tk.X)

        ttk.Label(name_frame, text="Mẫu tên bài hát đơn lẻ (--name-format):", style="Card.TLabel").pack(anchor="w")
        entry_nf = tk.Entry(name_frame, textvariable=self.var_name_format, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_nf.pack(fill=tk.X, pady=(2, 6), ipady=3)

        ttk.Label(name_frame, text="Mẫu tên bài trong Playlist (--playlist-name-format):", style="Card.TLabel").pack(anchor="w")
        entry_pnf = tk.Entry(name_frame, textvariable=self.var_pl_name_format, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_pnf.pack(fill=tk.X, pady=(2, 6), ipady=3)

        preset_row = ttk.Frame(name_frame, style="Card.TFrame")
        preset_row.pack(fill=tk.X, pady=4)
        ttk.Label(preset_row, text="Mẫu nhanh:", style="Muted.TLabel").pack(side=tk.LEFT, padx=(0, 6))

        btn_p1 = ttk.Button(preset_row, text="Mặc định", style="Outline.TButton", command=lambda: self._set_name_preset(1))
        btn_p1.pack(side=tk.LEFT, padx=3)
        btn_p2 = ttk.Button(preset_row, text="Chỉ Tiêu Đề", style="Outline.TButton", command=lambda: self._set_name_preset(2))
        btn_p2.pack(side=tk.LEFT, padx=3)
        btn_p3 = ttk.Button(preset_row, text="Thứ Tự - Nghệ Sĩ - Bài Hát", style="Outline.TButton", command=lambda: self._set_name_preset(3))
        btn_p3.pack(side=tk.LEFT, padx=3)

    def _set_name_preset(self, p_type):
        if p_type == 1:
            self.var_name_format.set("{user[username]} - {title}")
            self.var_pl_name_format.set("{playlist[tracknumber]} - {title}")
        elif p_type == 2:
            self.var_name_format.set("{title}")
            self.var_pl_name_format.set("{title}")
        elif p_type == 3:
            self.var_name_format.set("{user[username]} - {title}")
            self.var_pl_name_format.set("{playlist[tracknumber]} - {user[username]} - {title}")

    # --------------------------------------------------------------------------
    # TAB 4: NÂNG CAO & XÁC THỰC
    # --------------------------------------------------------------------------
    def _build_tab_advanced(self):
        tab = ttk.Frame(self.notebook, style="Card.TFrame", padding=12)
        self.notebook.add(tab, text=" ⚙️ Nâng Cao & Xác Thực ")

        col1 = ttk.Frame(tab, style="Card.TFrame")
        col1.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 8))

        col2 = ttk.Frame(tab, style="Card.TFrame")
        col2.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(8, 0))

        # Kiểm soát ghi đè & playlist
        ctrl_frame = ttk.LabelFrame(col1, text=" Quản Lý Tải & Tệp Trùng ", style="TLabelframe", padding=8)
        ctrl_frame.pack(fill=tk.X, pady=(0, 8))

        ttk.Checkbutton(ctrl_frame, text="Bỏ qua file đã tồn tại trên đĩa (-c)", variable=self.var_continue).pack(anchor="w", pady=2)
        ttk.Checkbutton(ctrl_frame, text="Ép buộc ghi đè file có sẵn (--overwrite)", variable=self.var_overwrite).pack(anchor="w", pady=2)
        ttk.Checkbutton(ctrl_frame, text="Không tạo thư mục con cho Playlist (--no-playlist-folder)", variable=self.var_no_pl_folder).pack(anchor="w", pady=2)
        ttk.Checkbutton(ctrl_frame, text="Chặn tải Playlist (chỉ tải track lẻ) (--no-playlist)", variable=self.var_no_playlist).pack(anchor="w", pady=2)
        ttk.Checkbutton(ctrl_frame, text="Dừng toàn bộ nếu 1 bài bị lỗi (--strict-playlist)", variable=self.var_strict_pl).pack(anchor="w", pady=2)

        # Hiệu năng đa luồng
        perf_frame = ttk.LabelFrame(col1, text=" Hiệu Năng & Đa Luồng Max Speed ", style="TLabelframe", padding=8)
        perf_frame.pack(fill=tk.X)

        ttk.Label(perf_frame, text="Số luồng kết nối phân đoạn (--concurrent-fragments):", style="Card.TLabel").pack(anchor="w")
        spin_frag = tk.Spinbox(perf_frame, from_=1, to=16, textvariable=self.var_concurrent_fragments, width=10, bg=self.colors["entry_bg"], fg="#ffffff", bd=1, relief=tk.SOLID)
        spin_frag.pack(anchor="w", pady=3)
        ttk.Label(perf_frame, text="Mặc định 4 luồng; tăng lên 8-16 để max speed HLS", style="Muted.TLabel").pack(anchor="w")

        # Xác thực tài khoản
        auth_frame = ttk.LabelFrame(col2, text=" Xác Thực & Ủy Quyền SoundCloud ", style="TLabelframe", padding=8)
        auth_frame.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(auth_frame, text="OAuth Token (--auth-token):", style="Card.TLabel").pack(anchor="w")
        entry_token = tk.Entry(auth_frame, textvariable=self.var_auth_token, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID, show="*")
        entry_token.pack(fill=tk.X, pady=2, ipady=2)

        ttk.Label(auth_frame, text="Client ID (--client-id):", style="Card.TLabel").pack(anchor="w", pady=(4, 0))
        entry_cid = tk.Entry(auth_frame, textvariable=self.var_client_id, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_cid.pack(fill=tk.X, pady=2, ipady=2)
        ttk.Label(auth_frame, text="Để trống hệ thống sẽ tự sinh Client ID tự động", style="Muted.TLabel").pack(anchor="w")

        # Tùy chọn mở rộng
        extra_frame = ttk.LabelFrame(col2, text=" Tham Số yt-dlp & Lịch Sử ", style="TLabelframe", padding=8)
        extra_frame.pack(fill=tk.X)

        ttk.Label(extra_frame, text="Tham số bổ sung (--yt-dlp-args):", style="Card.TLabel").pack(anchor="w")
        entry_args = tk.Entry(extra_frame, textvariable=self.var_ytdlp_args, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_args.pack(fill=tk.X, pady=2, ipady=2)

        ttk.Label(extra_frame, text="File lịch sử tải (--download-archive):", style="Card.TLabel").pack(anchor="w", pady=(4, 0))
        entry_arch = tk.Entry(extra_frame, textvariable=self.var_archive, bg=self.colors["entry_bg"], fg="#ffffff", insertbackground="#ffffff", bd=1, relief=tk.SOLID)
        entry_arch.pack(fill=tk.X, pady=2, ipady=2)

        debug_row = ttk.Frame(extra_frame, style="Card.TFrame")
        debug_row.pack(fill=tk.X, pady=(4, 0))
        ttk.Checkbutton(debug_row, text="Bật Debug Log (--debug)", variable=self.var_debug).pack(side=tk.LEFT)
        ttk.Checkbutton(debug_row, text="Ẩn cảnh báo (--hidewarnings)", variable=self.var_hidewarnings).pack(side=tk.LEFT, padx=10)

    # --------------------------------------------------------------------------
    # THAO TÁC TIỆN ÍCH
    # --------------------------------------------------------------------------
    def _paste_clipboard(self):
        try:
            text = self.root.clipboard_get()
            if text:
                self.var_url.set(text.strip())
        except Exception:
            pass

    def _browse_folder(self):
        curr = self.var_path.get()
        init_dir = curr if os.path.exists(curr) else str(Path.home())
        selected = filedialog.askdirectory(initialdir=init_dir, title="Chọn thư mục lưu nhạc")
        if selected:
            self.var_path.set(selected)

    def _open_download_folder(self):
        path = self.var_path.get()
        if not os.path.exists(path):
            try:
                os.makedirs(path, exist_ok=True)
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể tạo thư mục:\n{e}")
                return

        try:
            if sys.platform == "win32":
                os.startfile(path)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception as e:
            self._log(f"❌ Không thể mở thư mục: {e}")

    def _clear_log(self):
        self.txt_log.delete("1.0", tk.END)

    def _log(self, msg: str):
        self.txt_log.insert(tk.END, msg + "\n")
        # Giới hạn tối đa 500 dòng nhật ký chống tràn RAM
        lines = int(self.txt_log.index("end-1c").split(".")[0])
        if lines > 500:
            self.txt_log.delete("1.0", f"{lines - 500}.0")
        if self.var_autoscroll.get():
            self.txt_log.see(tk.END)

    # --------------------------------------------------------------------------
    # THU THẬP ĐỐI SỐ & BẮT ĐẦU TẢI (IN-PROCESS WORKER)
    # --------------------------------------------------------------------------
    def _collect_args(self) -> Optional[dict]:
        url = self.var_url.get().strip()
        mode = self.var_mode.get()

        if not url and mode != "me":
            messagebox.showwarning("Thiếu dữ liệu", "Vui lòng nhập đường dẫn SoundCloud hoặc từ khóa tìm kiếm!")
            return None

        # Ràng buộc đường dẫn lưu
        save_path = self.var_path.get().strip()
        if not save_path:
            save_path = self.default_save_path
            self.var_path.set(save_path)
        os.makedirs(save_path, exist_ok=True)

        args = {
            "url": url,
            "mode": mode,
            "is_search": self.var_is_search.get(),
            "path": Path(save_path),
            "o": self.var_offset.get().strip() or None,
            "name_format": self.var_name_format.get().strip() or "{user[username]} - {title}",
            "playlist_name_format": self.var_pl_name_format.get().strip() or "{playlist[tracknumber]} - {title}",
            "onlymp3": self.var_onlymp3.get(),
            "flac": self.var_flac.get(),
            "opus": self.var_opus.get(),
            "min_size": self.var_min_size.get().strip() or None,
            "max_size": self.var_max_size.get().strip() or None,
            "force_metadata": self.var_force_meta.get(),
            "original_metadata": self.var_orig_meta.get(),
            "extract_artist": self.var_extract_artist.get(),
            "no_album_tag": self.var_no_album_tag.get(),
            "original_art": self.var_orig_art.get(),
            "original_name": self.var_orig_name.get(),
            "add_description": self.var_add_desc.get(),
            "c": self.var_continue.get(),
            "overwrite": self.var_overwrite.get(),
            "no_playlist_folder": self.var_no_pl_folder.get(),
            "no_playlist": self.var_no_playlist.get(),
            "strict_playlist": self.var_strict_pl.get(),
            "auth_token": self.var_auth_token.get().strip() or None,
            "client_id": self.var_client_id.get().strip() or None,
            "download_archive": self.var_archive.get().strip() or None,
            "sync": self.var_sync.get().strip() or None,
            "yt_dlp_args": self.var_ytdlp_args.get().strip() or "",
            "debug": self.var_debug.get(),
            "hidewarnings": self.var_hidewarnings.get(),
        }

        # Xử lý cờ file gốc
        orig_choice = self.var_original_choice.get()
        if orig_choice == "only":
            args["only_original"] = True
            args["no_original"] = False
        elif orig_choice == "none":
            args["only_original"] = False
            args["no_original"] = True
        else:
            args["only_original"] = False
            args["no_original"] = False

        # Mode tương ứng
        if mode not in ("-l", "me"):
            args[mode.strip("-")] = True

        # Đa luồng phân đoạn HLS
        frag = self.var_concurrent_fragments.get().strip()
        if frag and frag.isdigit() and int(frag) > 1:
            frag_arg = f"--concurrent-fragments {frag}"
            if frag_arg not in args["yt_dlp_args"]:
                args["yt_dlp_args"] = f"{args['yt_dlp_args']} {frag_arg}".strip()

        return args

    def _start_download(self):
        if not YTDLP_AVAILABLE or not SOUNDCLOUD_AVAILABLE:
            self._warn_missing_deps()
            return

        args = self._collect_args()
        if not args:
            return

        self._save_settings()  # Ghi nhớ tùy chọn người dùng ngay khi bắt đầu tải

        self.abort_event.clear()
        self.is_downloading = True
        self.btn_download.config(state=tk.DISABLED)
        self.btn_abort.config(state=tk.NORMAL)
        self.var_status.set("Đang tải dữ liệu...")
        self.lbl_badge.config(bg=self.colors["primary"])
        self.progress_bar.config(value=0)

        self._log("=" * 60)
        self._log("🚀 Khởi chạy tác vụ tải SoundCloud...")
        if args["o"]:
            self._log(f"📌 Thiết lập Offset/Phân đoạn: {args['o']}")

        # Chạy trong luồng phụ an toàn
        worker_thread = threading.Thread(target=self._download_worker, args=(args,), daemon=True)
        worker_thread.start()

    def _abort_download(self):
        if self.is_downloading:
            self.abort_event.set()
            self._log("⚠️ Đang gửi tín hiệu dừng tới động cơ tải...")
            self.var_status.set("Đang dừng...")
            self.btn_abort.config(state=tk.DISABLED)

    def _download_worker(self, scdl_args: dict):
        try:
            if self.abort_event.is_set():
                raise AbortDownloadException("Người dùng đã hủy trước khi bắt đầu tải.")

            # 1. Khởi tạo SoundCloud Client
            client_id = scdl_args.get("client_id")
            token = scdl_args.get("auth_token")

            # Đọc Client ID từ cache cấu hình để tránh mất 8s phân tích lại
            cache_file = Path.home() / ".config" / "scdl" / "scdl.cfg"
            if not client_id and cache_file.exists():
                try:
                    cp = configparser.ConfigParser()
                    cp.read(cache_file, encoding="utf-8")
                    cached_cid = cp.get("scdl", "client_id", fallback="")
                    if cached_cid:
                        client_id = cached_cid
                except Exception:
                    pass

            client = SoundCloud(client_id, token if token else None)

            if not client.is_client_id_valid():
                self._post_ui(self._log, "🔑 Client ID chưa có hoặc đã hết hạn, đang tạo Client ID động...")
                client = SoundCloud(None, token if token else None)
                if not client.is_client_id_valid():
                    raise RuntimeError("Không thể tạo Client ID động từ SoundCloud.")
                self._post_ui(self._log, f"✅ Đã tạo Client ID động thành công: {client.client_id}")

                # Ghi nhớ Client ID vào cache để khởi chạy tức thì ở các lần sau
                try:
                    cache_file.parent.mkdir(parents=True, exist_ok=True)
                    cp = configparser.ConfigParser()
                    if cache_file.exists():
                        cp.read(cache_file, encoding="utf-8")
                    if not cp.has_section("scdl"):
                        cp.add_section("scdl")
                    cp.set("scdl", "client_id", client.client_id)
                    with open(cache_file, "w", encoding="utf-8") as f:
                        cp.write(f)
                except Exception:
                    pass

            scdl_args["client_id"] = client.client_id

            if self.abort_event.is_set():
                raise AbortDownloadException("Người dùng đã hủy trước khi bắt đầu tải.")

            # 2. Xử lý URL đầu vào
            url = scdl_args["url"]
            if scdl_args["mode"] == "me":
                me = client.get_me()
                if not me:
                    raise RuntimeError("Không thể lấy thông tin tài khoản 'me'. Kiểm tra lại Auth Token!")
                url = me.permalink_url
            elif scdl_args["is_search"]:
                resolved_url = search_soundcloud_url(
                    client, url, log_fn=lambda m: self._post_ui(self._log, m), abort_event=self.abort_event
                )
                if not resolved_url:
                    if self.abort_event.is_set():
                        raise AbortDownloadException("Người dùng đã hủy quá trình tìm kiếm.")
                    raise RuntimeError("Tìm kiếm không có kết quả phù hợp.")
                url = resolved_url

            if self.abort_event.is_set():
                raise AbortDownloadException("Người dùng đã hủy trước khi bắt đầu tải.")

            # 3. Biên dịch tham số sang yt-dlp
            download_url_target, ytdl_params, postprocessors = build_engine_params(url, scdl_args)

            # 4. Gắn Logger và Progress Hooks thời gian thực
            gui_logger = GUIYTLogger(
                log_cb=lambda m: self._post_ui(self._log, m),
                debug_mode=scdl_args.get("debug", False),
                hide_warnings=scdl_args.get("hidewarnings", False),
                abort_event=self.abort_event,
            )
            ytdl_params["logger"] = gui_logger

            def progress_hook(d):
                if self.abort_event.is_set():
                    raise AbortDownloadException("Người dùng đã hủy quá trình tải.")

                status = d.get("status")
                if status == "downloading":
                    filename = os.path.basename(d.get("filename", ""))
                    percent_str = d.get("_percent_str", "0%").strip()
                    speed_str = d.get("_speed_str", "--").strip()
                    eta_str = d.get("_eta_str", "--").strip()

                    downloaded = d.get("downloaded_bytes") or 0
                    total = d.get("total_bytes") or d.get("total_bytes_estimate") or 0
                    p_val = (downloaded / total * 100) if total > 0 else 0

                    self._post_ui(self._update_progress, filename, p_val, percent_str, speed_str, eta_str)
                elif status == "finished":
                    filename = os.path.basename(d.get("filename", ""))
                    self._post_ui(self._update_track_finished, filename)

            ytdl_params["progress_hooks"] = [progress_hook]

            # Gắn match_filter dừng toàn bộ playlist ngay khi nhận cờ abort
            existing_match_filter = ytdl_params.get("match_filter")
            def abort_match_filter(info_dict, incomplete=False):
                if self.abort_event.is_set():
                    raise AbortDownloadException("Người dùng đã hủy quá trình tải.")
                if existing_match_filter:
                    try:
                        return existing_match_filter(info_dict, incomplete=incomplete)
                    except TypeError:
                        return existing_match_filter(info_dict)
                return None
            ytdl_params["match_filter"] = abort_match_filter

            # Xử lý yt-dlp args tùy chỉnh
            yt_dlp_args_custom = scdl_args.get("yt_dlp_args")
            if yt_dlp_args_custom:
                argv = shlex.split(yt_dlp_args_custom)
                overrides = cli_to_api(argv)
                ytdl_params = {**ytdl_params, **overrides}

            # Lọc bỏ Mutagen trùng lặp nếu có
            ytdl_params["postprocessors"] = [
                pp for pp in ytdl_params.get("postprocessors", []) if pp.get("key") not in ("EmbedThumbnail", "FFmpegMetadata")
            ]

            # 5. Thực thi YoutubeDL In-process
            with YoutubeDL(ytdl_params) as ydl:
                ydl._abort_event = self.abort_event

                # Intercept urlopen để ngắt kết nối mạng ngay lập tức khi người dùng bấm Hủy
                old_urlopen = ydl.urlopen
                def _checked_urlopen(req):
                    if self.abort_event.is_set():
                        raise AbortDownloadException("Người dùng đã hủy quá trình tải.")
                    return old_urlopen(req)
                ydl.urlopen = _checked_urlopen

                if scdl_args.get("client_id"):
                    ydl.cache.store("soundcloud", "client_id", scdl_args["client_id"])
                for pp, when in postprocessors:
                    ydl.add_post_processor(pp, when)

                sync_helper = SyncDownloadHelper(scdl_args, ydl)
                ydl.download([download_url_target])
                sync_helper.post_download()

            self._post_ui(self._on_download_complete, True, "✅ Quá trình tải hoàn tất thành công!")
        except (AbortDownloadException, DownloadCancelled):
            self._post_ui(self._on_download_complete, False, "⏹ Tiến trình đã được dừng theo yêu cầu của bạn.")
        except Exception as e:
            err_msg = str(e)
            if "AbortDownloadException" in err_msg or "DownloadCancelled" in err_msg or self.abort_event.is_set():
                self._post_ui(self._on_download_complete, False, "⏹ Tiến trình đã được dừng theo yêu cầu của bạn.")
            else:
                self._post_ui(self._on_download_complete, False, f"❌ Lỗi: {err_msg}")
        finally:
            self._post_ui(self._ensure_idle_state)

    # --------------------------------------------------------------------------
    # ĐỒNG BỘ GIAO DIỆN TỪ LUỒNG PHỤ (THREAD-SAFE DISPATCHING)
    # --------------------------------------------------------------------------
    def _ensure_idle_state(self):
        if self.is_downloading:
            self.is_downloading = False
            self.btn_download.config(state=tk.NORMAL)
            self.btn_abort.config(state=tk.DISABLED)

    def _update_progress(self, filename, percent_val, percent_str, speed_str, eta_str):
        self.var_progress_track.set(f"Đang tải: {filename}")
        self.var_progress_metrics.set(f"Tốc độ: {speed_str} | ETA: {eta_str} | Tiến độ: {percent_str}")
        self.progress_bar.config(value=percent_val)

    def _update_track_finished(self, filename):
        self.var_progress_track.set(f"Đã tải xong: {filename}")
        self.progress_bar.config(value=100)
        self._log(f"🎉 Hoàn thành: {filename}")

    def _on_download_complete(self, success: bool, message: str):
        self.is_downloading = False
        self.btn_download.config(state=tk.NORMAL)
        self.btn_abort.config(state=tk.DISABLED)

        if success:
            self.var_status.set("Hoàn thành")
            self.lbl_badge.config(bg=self.colors["success"])
            self.var_progress_metrics.set("Tất cả bài hát đã tải hoàn tất.")
        else:
            if self.abort_event.is_set():
                self.var_status.set("Đã dừng")
                self.lbl_badge.config(bg=self.colors["danger"])
                self.var_progress_track.set("Đã dừng tác vụ")
                self.var_progress_metrics.set("Người dùng đã hủy quá trình tải.")
            else:
                self.var_status.set("Gặp lỗi")
                self.lbl_badge.config(bg=self.colors["danger"])

        self._log(message)
        self._log("=" * 60)


# ==============================================================================
# ĐIỂM VÀO THỰC THI (ENTRY POINT)
# ==============================================================================
if __name__ == "__main__":
    # Tự động ẩn cửa sổ console đen (CMD) trên Windows nếu khởi chạy bằng python.exe
    if sys.platform == "win32":
        try:
            import ctypes
            hwnd = ctypes.windll.kernel32.GetConsoleWindow()
            if hwnd:
                ctypes.windll.user32.ShowWindow(hwnd, 0)
        except Exception:
            pass

    root = tk.Tk()
    app = ModernSCDLApp(root)
    root.mainloop()