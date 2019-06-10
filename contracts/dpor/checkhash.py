#!/usr/bin/env python3
import sys
import os
import hashlib

os.chdir(os.path.dirname(os.path.abspath(__file__)))


def check_hash(items):
    for fname, fhash in items:
        m = hashlib.md5()
        m.update(open(fname, "rb").read())
        h = m.digest().hex()
        if h != fhash:
            print("file modified:", fname, " hash:", h, " expected:", fhash)
            sys.exit(1)


def libs_hash():
    safe_math = "7f3a15a26f34764a783e6f8702d5529a"
    set_ = "201ea38c4afe5258bc7a17ce19e0f48b"
    libs = [
        #  (filename, expected hashsum)
        ("campaign/lib/safeMath.sol", safe_math),
        ("rnode/lib/safeMath.sol", safe_math),
        ("rnode/lib/set.sol", set_),
    ]
    assert len(libs) == 3
    return libs



def main():
    check_hash(libs_hash())


if __name__ == '__main__':
    main()
