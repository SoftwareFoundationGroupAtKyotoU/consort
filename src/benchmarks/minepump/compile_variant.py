import hashlib, os, sys
import tempfile
import argparse

lib_files = [
    "environment.imp",
    "main.imp",
    "actions.imp"
]

def sort_files(a, b):
    if a == b:
        return 0
    elif a.endswith("main.imp"):
        return 1
    elif b.endswith("main.imp"):
        return -1
    elif a < b:
        return -1
    else:
        return 1

def splat(f_name):
    vdir = os.path.dirname(f_name)
    parent_dir = os.path.join(vdir, "..", "..")
    sys_files = [
        os.path.join(parent_dir, sf) for sf in lib_files
    ]
    files = sorted([ f_name ] + sys_files, cmp = sort_files)
    file_hash = hashlib.new("md5")
    new_contents = ""
    for l in files:
        with open(l) as f:
            c = "##pos \"%s\" 1\n" % os.path.realpath(l) + f.read()
            file_hash.update(c)
            new_contents += c
    hashstr = file_hash.hexdigest()
    tdir = tempfile.gettempdir()
    o_file = os.path.join(tdir, "mpump_%s.imp" % hashstr)
    with open(o_file, 'w') as f:
        print >> f, new_contents
    return o_file

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("variant", type=str)
    args = parser.parse_args()
    print splat(args.variant)
