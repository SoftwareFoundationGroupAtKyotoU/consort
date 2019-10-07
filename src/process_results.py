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

with open(sys.argv[2], 'w') as result_table:
    print >> result_table, r'\begin{tabular}{cc||cc||cccc}\toprule'
    print >> result_table, r'\textbf{Set} & \textbf{N. Tests} & \multicolumn{2}{l}{\textbf{\name}} & \multicolumn{4}{c}{\textbf{JayHorn}} \\'
    print >> result_table, r'& & \emph{Correct} & \emph{T/O} & \emph{Correct} & \emph{T/O} & \emph{Err.} & \emph{Imprecise} \\ \midrule'
    print >> result_table, r'\textbf{Safe} & %d & %d & %d &  %d &  %d &  %d & %d \\' % (
        sat_correct + sat_timeout, sat_correct, sat_timeout,
        (sat_correct + sat_timeout) - sat_out_performed, sat_finished, sat_robustness, sat_precise
    )
    print >> result_table, r'\textbf{Unsafe} & %d & %d & %d &  %d &  %d &  %d & %d' % (
        unsat_correct + unsat_timeout, unsat_correct, unsat_timeout,
        (unsat_correct + unsat_timeout) - unsat_out_performed, unsat_finished, unsat_robustness, unsat_precise
    )
    print >> result_table, r'\end{tabular}'

with open(sys.argv[3], 'w') as consort_table:
    print >> consort_table, r'\begin{tabular}{ccc}\toprule'
    print >> consort_table, r'\textbf{Name} & \textbf{Verified?} & \textbf{Time} \\ \midrule'
    l = sorted(data["consort"], key = lambda d: d["name"])
    for d in l:
        assert d["result"]
        print >> consort_table, r'\textbf{%s} & \checkmark & %0.2f \\' % (d["name"], d["elapsed"])
    print >> consort_table, r'\end{tabular}'

def print_bench_line(benchmark_table, nm, stat):
    b = [ stat["incl"], stat["java"], stat["incomplete"], stat["broken"] ]
    b = [ sum(b) ] + b    
    print >> benchmark_table, nm + " & " + " & ".join(map(str, b))

with open(sys.argv[4], 'w') as benchmark_table:
    print >> benchmark_table, r'\begin{tabular}{cccccc}\toprule'
    print >> benchmark_table, r'\textbf{Set} & \textbf{Orig. Tests} & \textbf{Adapted} & \textbf{Java} & \textbf{Inc} & \textbf{Bug} \\ \midrule'
    print_bench_line(benchmark_table, "Safe", test_stat["sat"])
    print >> benchmark_table, r'\\'
    print_bench_line(benchmark_table, "Unsafe", test_stat["unsat"])
    print >> benchmark_table, r'\end{tabular}'
