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
    set_ = "1ec6f5b54628a5249ffdbd3b3058caa6"
    primite_contracts = "bb363a54bd3e6cb98f5265635f125234"
    libs = [
        #  (filename, expected hashsum)
        ("campaign/lib/safeMath.sol", safe_math),
        ("campaign/lib/set.sol", set_),
        ("rnode/lib/safeMath.sol", safe_math),
        ("rnode/lib/set.sol", set_),
    ]
    assert len(libs) == 4
    return libs



def main():
    check_hash(libs_hash())


if __name__ == '__main__':
    main()
