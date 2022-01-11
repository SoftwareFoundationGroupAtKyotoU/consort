#!/usr/bin/env python3

import sys
import subprocess
import tempfile
import atexit, shutil, os
import argparse
import time

def log_command(args, cmd):
    if args.verbose:
        import pipes
        print("executing:"," ".join([ pipes.quote(s) for s in cmd ]))

def run_silently(cmd, **kwargs):
    with open("/dev/null", "w") as out:
        s = time.time()
        subprocess.check_call(cmd, stdout = out, stderr = subprocess.STDOUT, **kwargs)
        e = time.time()
        return e - s

def print_done(args, e):
    if args.timing:
        print("done (in %.02f)" % e)
    else:
        print("done")

def main(this_dir, args):
    # 出力先のファイルのリセット
    path = "./src/main/java/edu/kyoto/fos/regnant/myTranslation/output/output.imp"

    with open(path, 'w') as f:
        pass

    f = open(path, "a")

    parser = argparse.ArgumentParser()
    parser.add_argument("--work-dir")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--jar")
    parser.add_argument("--skip-build", action="store_true", default = False)
    parser.add_argument("--debug-trans", action="store_true", default = False)
    parser.add_argument("--functional", action="store_true", default = False)
    parser.add_argument("--timing", action="store_true")
    parser.add_argument("--src-dir")
    parser.add_argument("--yaml")
    parser.add_argument("jdk8")
    parser.add_argument("entry_point")
    parser.add_argument("consort_args", nargs="*")
    # 追加
    parser.add_argument("--timeout", nargs="?", default="30")
    args = parser.parse_args(args)
    cls = args.entry_point
    if args.src_dir is None and args.jar is None:
        print("Need at least source or jar")
        return 1

    if args.debug_trans:
        args.verbose = True

    if not args.skip_build:
        run_silently(["gradle", "installDist"], cwd = this_dir)

    if args.work_dir is None:
        work_dir = tempfile.mkdtemp()
        atexit.register(lambda: shutil.rmtree(work_dir))
    else:
        work_dir = args.work_dir

    if args.jar is None:
        assert args.src_dir is not None
        cls_dir = os.path.join(work_dir, "classes")
        if not os.path.exists(cls_dir):
            os.makedirs(cls_dir)

        source_file = cls.replace(".", "/") + ".java"

        compile_command = ["javac", "-g:lines,vars", "-source", "8", "-target", "8", "-d", cls_dir, args.src_dir + "/" + source_file]
        log_command(args, compile_command)
        print("compiling source java...", end=' ')
        sys.stdout.flush()
        run_silently(compile_command)
        print("done")
    else:
        cls_dir = args.jar

    flags = os.path.join(work_dir, "control.sexp")
    data = os.path.join(work_dir, "mono.imp")

    # 自分のアウトプットのパスを追加
    my_data = "./src/main/java/edu/kyoto/fos/regnant/myTranslation/output/output.imp"

    regnant_options = "enabled:true,output:%s,flags:%s" % (data, flags)

    if args.functional:
        regnant_options += ",model:functional"

    run_script = os.path.join(this_dir, "build/install/regnant/bin/regnant")

    rt_path = os.path.join(args.jdk8, "Contents/Home/lib/rt.jar")

    regnant_command = [
        run_script,
        "-f", "n", # no output
        "-no-bodies-for-excluded", # don't load the JCL (for now)
        "-w", # whole program mode
        "-p", "cg.spark", "on", # run points to analysis
#        "-p", "jb", "use-original-names:true", # try to make our names easier
        "-soot-class-path", cls_dir + ":" + rt_path, # where to find the test file
        "-p", "wjtp.regnant", regnant_options,
        cls # the class to run on
    ]

    log_command(args, regnant_command)
    if args.debug_trans:
        return subprocess.call(regnant_command)
    print("Translating java bytecode...", end=' ')
    sys.stdout.flush()
    el = run_silently(regnant_command)
    print_done(args, el)

    print("Generating control flags...", end=' ')
    sys.stdout.flush()
    intr_loc = os.path.join(work_dir, "java.intr")

    intr_command = [
        os.path.join(this_dir, "../_build/default/genFlags.exe"),
        os.path.join(this_dir, "../stdlib/lin.intr"),
        flags,
        intr_loc,
        "generated.smt"
    ]
    log_command(args, intr_command)
    el = run_silently(intr_command)
    print_done(args, el)

    # 出力先のファイルにエントリーポイントを追加
    f.write("{ f0() }")
    f.close()

    print("Running ConSORT on translated program:")
    yaml_flg = ["-yaml"] if args.yaml is not None else []
    consort_cmd = [
        os.path.join(this_dir, "../_build/default/test.exe"),
        "-intrinsics", intr_loc,
        "-exit-status",
        "-timeout", args.timeout
    ] + args.consort_args + yaml_flg + [
        data
    ]
    log_command(args, consort_cmd)
    s = time.time()
    ret = subprocess.run(consort_cmd, stdout = subprocess.PIPE)
    e = time.time()

    if args.yaml:
        with open(args.yaml, 'w') as out:
            print(ret.stdout.decode("utf-8"), file=out)
        print("Done")
    else:
        print(ret.stdout.decode("utf-8").strip())
    if args.timing:
        print("(ConSORT ran for %.02f seconds)" % (e - s))

    # 自分の Regnant で実行
    print("Running ConSORT with new Regnant on translated program:")
    consort_cmd = [os.path.join(this_dir, "../test.sh"), "-timeout", args.timeout, my_data]
    log_command(args, consort_cmd)
    my_s = time.time()
    ret = subprocess.run(consort_cmd, stdout = subprocess.PIPE)
    my_e = time.time()

    print(ret.stdout.decode("utf-8").strip())

    if args.timing:
        print("(ConSORT with new Regnant ran for %.02f seconds)" % (my_e - my_s))

    return ret.returncode

if __name__ == "__main__":
    sys.exit(main(os.path.realpath(os.path.dirname(sys.argv[0])), sys.argv[1:]))
