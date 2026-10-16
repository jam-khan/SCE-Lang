#!/usr/bin/env python3
"""Serve the playground and API docs assembled by `make site` in _build/site.
Use the Wasm MIME type required for streaming compilation."""
import http.server
import os
import sys

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
ROOT = os.path.join(os.path.dirname(__file__), "..", "_build", "site")


class Handler(http.server.SimpleHTTPRequestHandler):
    extensions_map = {
        **http.server.SimpleHTTPRequestHandler.extensions_map,
        ".wasm": "application/wasm",
        ".js": "text/javascript",
    }

    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=ROOT, **kwargs)


if __name__ == "__main__":
    if not os.path.isfile(os.path.join(ROOT, "index.html")):
        sys.exit("Site not built; run `make site` or `make web` first.")
    with http.server.ThreadingHTTPServer(("127.0.0.1", PORT), Handler) as srv:
        print(f"SCE playground at http://127.0.0.1:{PORT}")
        srv.serve_forever()
