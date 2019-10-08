import argparse
import sys
import os
import yaml
import subprocess
import time

def partition(l, key):
    a = []
    b = []
    for e in l:
        if key(e):
            a.append(e)
        else:
            b.append(e)
    return a,b

def get_tag(f_name, root = None):
    if root is not None:
        f_name = os.path.join(root, f_name)
    with open(f_name, 'r') as f:
        first_line = f.readline().strip()
        if first_line.startswith("/**") and first_line.endswith("*/"):
            return first_line[len("/** "):-len("*/")].strip()
        else:
            return None

def run_silent(c, **kwargs):
    with open(os.devnull, 'w') as o:
        subprocess.check_call(c, stdout = o, stderr = o, **kwargs)

def build_consort(root):
    print "Building consort..."
    run_silent(["dune", "build", "test.exe"], cwd = root)
    run_silent(["dune", "build", "genLin.exe"], cwd = root)
    lin_path = os.path.join(root, "_build", "default", "genLin.exe")
    stdlib_path = os.path.join(root, "stdlib", "lin.intr")
    run_silent([lin_path, stdlib_path, "lin-std.smt"], cwd = root)
    print "... Done"

def mk_result(res, time, **kwargs):
    to_ret = { "result": res, "elapsed": time }
    for (k,v) in kwargs.iteritems():
        to_ret[k] = v
    return to_ret

def run_jayhorn_with_timeout(config, tmp_dir):
    jayhorn_jar = config["jayhorn"]
    start = time.time()
    with open(os.devnull, 'w') as f:
        p = subprocess.Popen([
            "timeout",
            "%ds" % config["timeout"],
            "java",
            "-jar", jayhorn_jar,
            "-j",
            tmp_dir
        ], stderr = f, stdout = subprocess.PIPE)
    (o,e) = p.communicate()
    end = time.time() 
    if p.returncode == 124:
        return mk_result(False, end - start, reason = "(timeout)")
    if p.returncode != 0:
        return mk_result(False, end - start, reason = "(error)")
    o_lines = o.strip().split("\n")
    last = o_lines[-1]
    if last == "SAFE":
        return mk_result(True, end - start)
    elif last == "UNSAFE":
        return mk_result(False, end - start, reason = "(unsafe)")
    elif last == "UNKNOWN":
        return mk_result(False, end - start, reason = "(unknown)")
    else:
        raise RuntimeError("Do not know what to do with " + last)
    

def run_and_check_jayhorn(config, name):
    jayhorn_dir = config["jayhorn_bench"]["jayhorn_imp"]
    assert name.endswith(".imp")
    name = name[:-4]
    benchdir = os.path.join(jayhorn_dir, name)
    if not os.path.isdir(benchdir):
        print "Could not find jayhorn benchmark",name
        return None
    benchmain = os.path.join(benchdir, name + ".java")
    assert os.path.isfile(benchmain)
    tmp_dir = os.path.join(benchdir, "tmp")
    if not os.path.isdir(tmp_dir):
        os.makedirs(tmp_dir)
    # compile the benchmark
    run_silent([
        "javac", "-d", tmp_dir,
        "-sourcepath", benchdir,
        benchmain
    ])
    return run_jayhorn_with_timeout(config, tmp_dir)

def run_consort(config, benchimp):
    exe = os.path.join(config["consort"], "_build", "default", "test.exe")
    intr = os.path.join(config["consort"], "stdlib", "lin.intr")
    timeout = str(config["timeout"])
    exec_args = [
        exe,
        "-intrinsics", intr,
        "-timeout", timeout,
        "-solver", "parallel",
        benchimp
    ]
    with open(os.devnull, 'w') as null:
        start = time.time()
        out = subprocess.check_output(exec_args, stderr = null).strip()
        end = time.time()
    return (out, end - start)

def run_and_check(config, benchimp):
    print " - Running", benchimp
    (raw_result, elapse) = run_consort(config, benchimp)
    if raw_result.startswith("VERIFIED"):
        return mk_result(True, elapse, name = benchimp)
    else:
        assert raw_result.startswith("UNVERIFIED ")
        rest = raw_result[len("UNVERIFIED "):]
        return mk_result(False, elapse, reason = rest, name = benchimp)

def to_test_name(f):
    if f.endswith(".imp"):
        f = f[:-4]
    return f

def to_test_name_set(fs):
    return set([to_test_name(f) for f in fs ])

def collect_test_stats(config, consort_imp, sat, unsat, fail, trivial):
    missing_file = os.path.join(consort_imp, "missing.yml")
    exclude = {}
    if os.path.isfile(missing_file):
        with open(missing_file, 'r') as f:
            exclude = yaml.load(f)
    sat_s = to_test_name_set(sat)
    unsat_s = to_test_name_set(unsat)
    fail_s = to_test_name_set(fail)
    trivial_s = to_test_name_set(trivial)   
    
    class TestStat:
        def __init__(self):
            self.incl = 0
            self.incomplete = 0
            self.java_test = 0
            self.broken = 0
        def to_dict(self):
            return {
                "incl": self.incl,
                "incomplete": self.incomplete,
                "java": self.java_test,
                "broken": self.broken
            }

    sat_stat = TestStat()
    unsat_stat = TestStat()

    def classify_test(test_set, stat, tested):
        for j in test_set:
            if j in tested:
                stat.incl += 1
            elif j in exclude or j in trivial_s:
                stat.java_test += 1
            elif j in fail_s:
                t = get_tag(j + ".imp", consort_imp)
                if t == "fail: broken":
                    stat.broken += 1
                else:
                    stat.incomplete += 1
            else:
                print "Did you forget about",j

    tests = os.listdir(config["jayhorn_bench"]["jayhorn_imp"])
    jsat,junsat = partition(tests,key = lambda d: d.startswith("Sat"))
    classify_test(jsat, sat_stat, sat_s)
    classify_test(junsat, unsat_stat, unsat_s)
    return {
        "sat": sat_stat.to_dict(),
        "unsat": unsat_stat.to_dict()
    }

def run_jayhorn_bench(config):
    config_dir = config["path"]
    jayhorn_bench = config["jayhorn_bench"]
    consort_imp = jayhorn_bench["consort_imp"]
    
    if not os.path.isabs(consort_imp):
        consort_imp = os.path.join(config_dir, consort_imp)

    impl = [ s for s in os.listdir(consort_imp) if s.endswith(".imp") ]
    direct,adjusted = partition(impl, key = lambda k: not k.endswith("_CON.imp"))
    nontrivial,trivial = partition(direct, key = lambda k: get_tag(k,consort_imp) != "trivial")
    nofail,fail = partition(nontrivial, key = lambda k: (lambda g: g is None or not g.startswith("fail:"))(get_tag(k,consort_imp)))
    sat,unsat = partition(nofail, key = lambda k: k.startswith("Sat"))
    assert all([e.startswith("Unsat") for e in unsat ])
    build_consort(config["consort"])
    if os.path.isfile("/tmp/jayhornv.yml"):
        print "Using cached results, be sure this isn't the final paper run..."
        with open("/tmp/jayhornv.yml", 'r') as y:
            sat_result, unsat_result = yaml.load(y)
    else:
        print "Running positive tests... "
        sat_result = []
        unsat_result = []
        for s in sat:
            stat = run_and_check(config, os.path.join(consort_imp, s))
            stat["jayhorn"] = run_and_check_jayhorn(config, s)
            sat_result.append(stat)
        print "... Done"
        print "Running negative tests... "
        for u in unsat:
            stat = run_and_check(config, os.path.join(consort_imp, u))
            stat["jayhorn"] = run_and_check_jayhorn(config, config,u)
            unsat_result.append(stat)
        print "... Done"
        with open("/tmp/jayhornv.yml", 'w') as o:
            yaml.dump((sat_result, unsat_result), o)
    stats = collect_test_stats(config, consort_imp, sat, unsat, fail, trivial)
    return (sat_result,unsat_result,stats)

def run_consort_bench(config, bench_name):
    consort_res = []
    for l in config[bench_name]:
        f = l["path"]
        if not os.path.isabs(f):
            f = os.path.join(config["path"], f)
        d = run_and_check(config, f)
        d["name"] = l["name"]
        consort_res.append(d)
    return consort_res

def main(args):
    config = args.config
    if not os.path.isfile(config):
        print "Could not find experiement config at %s, aborting..." % config
        return 1
    with open(config, 'r') as f:
        config = yaml.load(f)
    if args.jayhorn is not None:
        config["jayhorn"] = args.jayhorn

    config["consort"] = args.consort

    if args.timeout is not None:
        config["timeout"] = args.timeout
    elif "timeout" not in config:
        config["timeout"] = 60
    config["path"] = os.path.dirname(args.config)
    jayhorn_results = run_jayhorn_bench(config)
    consort_results = run_consort_bench(config, "consort_bench")
    consort_neg_results = run_consort_bench(config, "consort_neg_bench")
    with open(args.output, 'w') as f:
        yaml.dump({"jayhorn": jayhorn_results, "consort": { "pos": consort_results, "neg": consort_neg_results }}, f)
    return 0

if __name__ == "__main__":
    parse = argparse.ArgumentParser()
    config_default = os.path.join(os.path.dirname(sys.argv[0]), "config.yml")
    root_default = os.path.join(os.path.dirname(sys.argv[0]))
    parse.add_argument("--config", help="File from which to read experiment config", default=config_default)
    parse.add_argument("--jayhorn", help="Override jayhorn repository location")
    parse.add_argument("--consort", help="Root folder containing consort", default=root_default)
    parse.add_argument("--timeout", help="Timeout", action="store", type = int)
    parse.add_argument("output", help="File in which to write output")

    args = parse.parse_args()
    sys.exit(main(args))
