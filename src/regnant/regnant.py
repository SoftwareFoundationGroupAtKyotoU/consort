#!/usr/bin/env python

import sys
import subprocess
import tempfile
import atexit, shutil, os
import argparse

def log_command(args, cmd):
    if args.verbose:
        import pipes
        print "executing:"," ".join([ pipes.quote(s) for s in cmd ])

def main(this_dir, args):
    parser = argparse.ArgumentParser()
    parser.add_argument("--work-dir")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("src_dir")
    parser.add_argument("entry_point")
    parser.add_argument("consort_args", nargs="*")
    args = parser.parse_args(args)
    entry = args.entry_point

    final_split = entry.rfind(".")

    cls = entry[:final_split]
    entry_method = entry[final_split + 1:]

    if args.work_dir is None:
        work_dir = tempfile.mkdtemp()
        atexit.register(lambda: shutil.rmtree(work_dir))
    else:
        work_dir = args.work_dir

    cls_dir = os.path.join(work_dir, "classes")
    if not os.path.exists(cls_dir):
        os.makedirs(cls_dir)

    source_file = cls.replace(".", "/") + ".java"

    compile_command = ["javac", "-g:lines,vars", "-d", cls_dir, args.src_dir + "/" + source_file]
    log_command(args, compile_command)
    print "compiling source java...",
    sys.stdout.flush()
    subprocess.check_call(compile_command)
    print "done"

    flags = os.path.join(work_dir, "control.sexp")
    data = os.path.join(work_dir, "mono.imp")

    regnant_options = "enabled:true,entry:%s,output:%s,flags:%s" % (entry_method, data, flags)

    cp = os.path.join(this_dir, "build/libs/regnant-with-deps.jar")

    regnant_command = [
        "java", "-ea", "-classpath", cp, "edu.kyoto.fos.regnant.Regnant",
        "-f", "n", # no output
        "-no-bodies-for-excluded", # don't load the JCL (for now)
        "-w", # whole program mode
        "-p", "cg.spark", "on", # run points to analysis
        "-p", "jb", "use-original-names:true", # try to make our names easier
        "-pp", # use our classpath for system classes
        "-soot-class-path", cls_dir, # where to find the test file
        "-p", "wjtp.regnant", regnant_options,
        cls # the class to run on
    ]

    log_command(args, regnant_command)
    print "Translating java bytecode...",
    sys.stdout.flush()
    with open("/dev/null", "w") as o:
        subprocess.check_call(regnant_command, stdout = o, stderr = o)
        print "done"
        print "Generating control flags...",
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
    subprocess.check_call(intr_command)
    print "done"
    print "Running ConSORT on translated program:"
    consort_cmd = [
        os.path.join(this_dir, "../_build/default/test.exe"),
        "-intrinsics", intr_loc,
        "-mode", "unified"
    ] + args.consort_args + [
        data
    ]
    log_command(args, consort_cmd)
    subprocess.call(consort_cmd)

if __name__ == "__main__":
    sys.exit(main(os.path.realpath(os.path.dirname(sys.argv[0])), sys.argv[1:]))
