#!/usr/bin/env python3

import argparse
import subprocess
from pathlib import Path
import sys
import tempfile
import yaml

# always be running
def run_corp(root, pref, suff):
    to_ret = {}
    for j in root.iterdir():
        if j.suffix != ".jar":
            continue
        with tempfile.NamedTemporaryFile() as f:
            cmd = pref + [
                "--jar", j.as_posix(),
                "--yaml", f.name
            ] + suff
            print("Testing", j)
            print("(Command:", " ".join(cmd), ")")
            subprocess.run(cmd, stdout = subprocess.PIPE)
            to_ret[j.name] = yaml.load(f.name)
    return to_ret

def main(argv):
    argp = argparse.ArgumentParser()
    argp.add_argument("--timeout", type=int)
    argp.add_argument("--solver", type=str, default="spacer")
    argp.add_argument("--regnant-root")
    argp.add_argument("jdk8")
    argp.add_argument("corpus")
    argp.add_argument("consort_args", nargs = "*")

    args = argp.parse_args(argv[1:])
    if args.regnant_root is not None:
        reg_root = Path(args.regnant_root)
    else:
        reg_root = Path(argv[0]).parent
    reg_script = reg_root.resolve() / "regnant.py"
    corp_root = Path(args.corpus)
    reg_args_pref = [
        reg_script.as_posix(),
        "--skip-build", "--functional"
    ]
    reg_args_suff = [
        args.jdk8,
        "minepump.Main",
        "--",
    ] + args.consort_args
    if args.timeout is not None:
        reg_args_suff += [ "-timeout", str(args.timeout) ]
    if args.solver is not None:
        reg_args_suff += [ "-solver", args.solver ]

    tr_res = run_corp(corp_root / "true", reg_args_pref, reg_args_suff)
    fl_res = run_corp(corp_root / "false", reg_args_suff, reg_args_suff)
    res = { "true": tr_res, "false": fl_res }
    print("done")
    print(yaml.dump(res))
    
if __name__ == "__main__":
    main(sys.argv)
