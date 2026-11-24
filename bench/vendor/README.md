# Vendored code

The benchmark's functions come from three open-source projects. Each folder holds
the upstream files at one commit, with the project's licence.

| Folder | Project | Commit | Licence |
|---|---|---|---|
| `cpython` | [python/cpython](https://github.com/python/cpython), tag `v3.14.10` | `b703b2c5e704341d61e367b9b940b77ed11dded0` | PSF, in `cpython/LICENSE` |
| `num-integer` | [rust-num/num-integer](https://github.com/rust-num/num-integer) | `765fd9b3eb9397471d41b9f613e530f6d9d6383f` | MIT or Apache 2.0, in `num-integer/LICENSE-*` |
| `es-toolkit` | [toss/es-toolkit](https://github.com/toss/es-toolkit) | `24e7a7b8cb8035fae1ea2e7b507aab96698a38b9` | MIT, in `es-toolkit/LICENSE` |

The files are unchanged, with one exception. `cpython/bisect.py` loses its last
`try: from _bisect import *` block. Upstream, that block replaces the Python
functions with their C versions. Without it, the Python code in the file is the
code that runs, so a seeded bug in it takes effect.

`cpython` holds `bisect.py`, `calendar.py` and `statistics.py` from `Lib/`.
`es-toolkit` holds seven files from `src/array` and `src/math`. `num-integer`
holds the crate's `Cargo.toml`, its `src/` and its licences.
