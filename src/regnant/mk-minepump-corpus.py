#!/usr/bin/env python3

import subprocess
import sys
import argparse
import os
import tempfile
import shutil
import atexit
import re
from pathlib import Path

def class_files(d):
    for f in d.iterdir():
        if f.is_dir():
            for m in class_files(f):
                yield m
        elif f.is_file() and f.suffix == ".class":
            yield f

def relativize(work_dir, g):
    for fl in g:
        yield "-C"
        yield work_dir.as_posix()
        yield fl.relative_to(work_dir).as_posix()

def main(argv):
    args = argparse.ArgumentParser()
    args.add_argument("minepump_root")
    args.add_argument("inst_root")
    args.add_argument("runtime_lib")
    args.add_argument("output")

    parsed = args.parse_args(argv[1:])
    work_dir = tempfile.mkdtemp("-reg-pump")
    work_dir = Path(work_dir)
    atexit.register(lambda: shutil.rmtree(work_dir.as_posix()))
    output = Path(parsed.output)

    tr_corp = output / "true"
    fl_corp = output / "false"
    tr_corp.mkdir(parents = True, exist_ok = True)
    fl_corp.mkdir(parents = True, exist_ok = True)

    # setup instrumented source
    tgt = Path(parsed.inst_root)
    tgt = work_dir / tgt.name
    inst_root = Path(parsed.inst_root)
    
    shutil.copytree(inst_root.as_posix(), tgt.as_posix())

    main = tgt / "Main.java"
    d = main.read_text()
    d = re.sub("^.*SkipTest.*$", "", d, flags = re.M)
    main.write_text(d)
    
    for product in Path(parsed.minepump_root).iterdir():
        print("Assembling %s" % product.name)
        if "true" in product.name:
            ct = tr_corp
        else:
            ct = fl_corp
        input_file = product / "MinePumpSystem" / "MinePump.java"
        d = input_file.read_text()
            
        d = re.sub(r'package\s+MinePumpSystem\s*;', "package minepump.MinePumpSystem;", d)
        d = re.sub(r'import\s+MinePumpSystem.Environment\s*;', '', d)
        output_file = tgt / "MinePumpSystem" / "MinePump.java"
        output_file.write_text(d)
        
        subprocess.check_output([
            "javac",
            "-source", "8",
            "-target", "8",
            "--source-path", work_dir.as_posix(),
            "--class-path", parsed.runtime_lib,
            main.as_posix()
        ], stderr = subprocess.STDOUT)
        to_jar = relativize(work_dir, class_files(work_dir))
        
        output_path = ct / (product.name + ".jar")
        subprocess.check_output([
            "jar", "cf", output_path.as_posix()
        ] + list(to_jar))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))
