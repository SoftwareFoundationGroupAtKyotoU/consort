import yaml
import sys

with open(sys.argv[1], 'r') as f:
    data = yaml.load(f)

(sat,unsat,test_stat) = data["jayhorn"]
sat_out_performed = 0
# when did we do better than jayhorn?
# we were more precise (correctly answering safe vs. their unsafe)
sat_precise = 0
# our tool didn't crash (theirs did)
sat_robustness = 0
# their tool spun out
sat_finished = 0

sat_correct = 0
sat_timeout = 0
sat_under_performed = 0
for s in sat:
    j = s["jayhorn"]
    if s["result"]:
        sat_correct += 1
        if not j["result"]:
            if j["reason"] == "(timeout)":
                sat_finished += 1
                sat_out_performed += 1
            elif j["reason"] == "(unsafe)" or j["reason"] == "(unknown)":
                sat_precise += 1
                sat_out_performed += 1
            elif j["reason"] == "(error)":
                sat_out_performed += 1
                sat_robustness += 1
            else:
                print "unhandled reason"
    else:
        if s["reason"] != "(timeout)":
            print "WARNING WARNING WARNING", s["name"]
        sat_timeout += 1
        if j["result"]:
            sat_under_performed += 1

unsat_correct = 0
unsat_timeout = 0
unsat_finished = 0
unsat_precise = 0
unsat_robustness = 0
unsat_out_performed = 0
for u in unsat:
    j = u["jayhorn"]
    if u["result"]:
        print "UNSOUND RESULT"
    else:
        if u["reason"] != "(unsafe)":
            print u["reason"]
            assert u["reason"] == "(timeout)"
            unsat_timeout += 1
        else:
            unsat_correct += 1

        if not j["result"]:
            if j["reason"] == "(timeout)":
                unsat_finished += 1
                sat_out_performed += 1
            elif j["reason"] == "(unknown)":
                unsat_precise += 1
                unsat_out_performed += 1
            elif j["reason"] == "(error)":
                unsat_out_performed += 1
                unsat_robustness += 1
            elif j["reason"] == "(unsafe)":
                # this is fine
                pass
            else:
                print "Unhandled reason", j["reason"]
        else:
            unsat_precise += 1
            unsat_out_performed += 1

def print_jayhorn_line(table, name, pref, nl = ''):
    # don't try this at home kids
    g = globals()
    correct = g[pref + "_correct"]
    timeout = g[pref + "_timeout"]
    out_performed = g[pref + "_out_performed"]
    finished = g[pref + "_finished"]
    robust = g[pref + "_robustness"]
    precision = g[pref + "_precise"]
    print >> table, r'\textbf{%s} & %d & %d & %d &  %d &  %d &  %d & %d%s' % (
        name,
        correct + timeout, correct, timeout,
        (correct + timeout) - out_performed, finished, robust, precision, nl
    )

def jayhorn_column(j):
    if j["result"]:
        return r'\checkmark'
    else:
        if j["reason"] == "(unsafe)":
            return r'\text{\sffamily X}'
        else:
            assert j["reason"] == "(timeout)"
            return r'\text{T/O}'

with open(sys.argv[2], 'w') as result_table:
    print >> result_table, r'\begin{tabular}{cc||cc||cccc}\toprule'
    print >> result_table, r'\textbf{Set} & \textbf{N. Tests} & \multicolumn{2}{l}{\textbf{\name}} & \multicolumn{4}{c}{\textbf{JayHorn}} \\'
    print >> result_table, r'& & \emph{Correct} & \emph{T/O} & \emph{Correct} & \emph{T/O} & \emph{Err.} & \emph{Imp.} \\ \midrule'
    print_jayhorn_line(result_table, "Safe", "sat", r'\\')
    print_jayhorn_line(result_table, "Unsafe", "unsat")
    print >> result_table, r'\end{tabular}'

with open(sys.argv[3], 'w') as consort_table:
    print >> consort_table, r'\begin{tabular}{lccc|lccc}\toprule'
    print >> consort_table, r'\textbf{Name} & \textbf{Verified?} & \textbf{Time} & \textbf{JayHorn} & \textbf{Buggy Name} & \textbf{Verified?} & \textbf{Time} & \textbf{JayHorn} \\ \midrule'
    neg_map = {}
    for d in data["consort"]["neg"]:
        neg_map[d["name"]] = d
    l = sorted(data["consort"]["pos"], key = lambda d: d["name"])
    for d in l:
        assert d["result"]
        print >> consort_table, r'\textbf{%s} & \checkmark & %0.2f & %s &' % (d["name"], d["elapsed"], jayhorn_column(d["jayhorn"]))
        n = d["name"]
        if n + "-BUG" in neg_map:
            nd = neg_map[n + "-BUG"]
            assert not nd["result"]
            print >> consort_table, r'\textbf{%s} & \text{\sffamily X} & %0.2f & %s \\' % (nd["name"], nd["elapsed"], jayhorn_column(nd["jayhorn"]))
        else:
            print >> consort_table, r' --- & --- & --- \\'
    print >> consort_table, r'\end{tabular}'

def print_bench_line(benchmark_table, nm, stat):
    b = [ stat["incl"], stat["java"], stat["incomplete"], stat["broken"] ]
    b = [ sum(b) ] + b    
    print >> benchmark_table, nm + " & " + " & ".join(map(str, b))

with open(sys.argv[4], 'w') as benchmark_table:
    print >> benchmark_table, r'\begin{tabular}{cccccc}\toprule'
    print >> benchmark_table, r'\textbf{Set} & \textbf{Orig.} & \textbf{Adapted} & \textbf{Java} & \textbf{Inc} & \textbf{Bug} \\ \midrule'
    print_bench_line(benchmark_table, "Safe", test_stat["sat"])
    print >> benchmark_table, r'\\'
    print_bench_line(benchmark_table, "Unsafe", test_stat["unsat"])
    print >> benchmark_table, r'\end{tabular}'
