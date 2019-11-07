import yaml
import sys

with open(sys.argv[1], 'r') as f:
    data = yaml.load(f)

(sat,unsat,test_stat) = data["jayhorn"]

sat_jayhorn_timeout = 0
sat_jayhorn_correct = 0
sat_jayhorn_imprecise = 0
sat_jayhorn_robustness = 0

sat_out_performed = 0
# when did we do better than jayhorn?
# we were more precise (correctly answering safe vs. their unsafe)
sat_precise = 0
# our tool didn't crash (theirs did)
sat_robustness = 0
# their tool spun out
sat_finished = 0

aliases = []

def interpret_jayhorn(j, stat_block, expect = True):
    if j["result"] == expect and (expect or j["reason"] == "(unsafe)"):
        stat_block["correct"] += 1
    else:
        if j["reason"] == "(timeout)":
            stat_block["timeout"] += 1
        elif j["reason"] == "(unsafe)" or j["reason"] == "(unknown)":
            stat_block["imprecise"] += 1
        elif j["reason"] == "(error)":
            stat_block["error"] += 1
        else:
            print "unhandled reason"

sat_correct = 0
sat_timeout = 0
sat_under_performed = 0
jayhorn_sat = {
    "correct": 0,
    "timeout": 0,
    "error": 0,
    "imprecise": 0
}
    
for s in sat:
    j = s["jayhorn"]
    aliases.append(s["alias"])
    if s["result"]:
        sat_correct += 1
    else:
        if s["reason"] != "(timeout)":
            print "WARNING WARNING WARNING", s["name"]
        sat_timeout += 1
        if j["result"]:
            sat_under_performed += 1
    interpret_jayhorn(j, jayhorn_sat)
    
unsat_correct = 0
unsat_timeout = 0
jayhorn_unsat = {
    "correct": 0,
    "timeout": 0,
    "error": 0,
    "imprecise": 0
}
for u in unsat:
    j = u["jayhorn"]
    aliases.append(u["alias"])
    if u["result"]:
        print "UNSOUND RESULT"
    else:
        if u["reason"] != "(unsafe)":
            print u["reason"]
            assert u["reason"] == "(timeout)"
            unsat_timeout += 1
        else:
            unsat_correct += 1
        interpret_jayhorn(j, jayhorn_unsat, expect = False)

print sat_under_performed

def print_jayhorn_line(table, name, pref, nl = ''):
    # don't try this at home kids
    g = globals()
    correct = g[pref + "_correct"]
    timeout = g[pref + "_timeout"]
    stat_block = g["jayhorn_" + pref]
    print >> table, r'\textbf{%s} & %d & %d & %d &  %d &  %d &  %d & %d%s' % (
        name,
        correct + timeout, correct, timeout,
        stat_block["correct"], stat_block["timeout"], stat_block["error"], stat_block["imprecise"], nl
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
    print >> result_table, r'\begin{tabular}{cccccccc}\toprule'
    print >> result_table, r'& & \multicolumn{2}{l}{\textbf{\name}} & \multicolumn{4}{c}{\textbf{JayHorn}} \\'
    print >> result_table, r'\cmidrule(lr){3-4} \cmidrule(lr){5-8}'
    print >> result_table, r'\textbf{Set} & \textbf{N. Tests} & \emph{Correct} & \emph{T/O} & \emph{Correct} & \emph{T/O} & \emph{Err.} & \emph{Imp.} \\ \midrule'
    print_jayhorn_line(result_table, "Safe", "sat", r'\\')
    print_jayhorn_line(result_table, "Unsafe", "unsat")
    print >> result_table, r'\end{tabular}'

with open(sys.argv[3], 'w') as consort_table:
    print >> consort_table, r'\begin{tabular}{lcccc|lcccc}\toprule'
    print >> consort_table, r'\textbf{Name} & \textbf{Safe?} & \textbf{Time(s)} & \textbf{Ann} & \textbf{JH} & \textbf{Name} & \textbf{Safe?} & \textbf{Time(s)} & \textbf{Ann} & \textbf{JH} \\ \midrule'
    neg_map = {}
    for d in data["consort"]["neg"]:
        neg_map[d["name"]] = d
    l = sorted(data["consort"]["pos"], key = lambda d: d["name"])
    for d in l:
        assert d["result"]
        print >> consort_table, r'\textbf{%s} & \checkmark & %0.2f & %d & %s &' % (d["name"], d["elapsed"], d["alias"], jayhorn_column(d["jayhorn"]))
        n = d["name"]
        if n + "-BUG" in neg_map:
            nd = neg_map[n + "-BUG"]
            assert not nd["result"]
            print >> consort_table, r'\textbf{%s} & \text{\sffamily X} & %0.2f & %d & %s \\' % (nd["name"], nd["elapsed"], nd["alias"], jayhorn_column(nd["jayhorn"]))
        else:
            print >> consort_table, r' &  & \\'
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

with open(sys.argv[5], 'w') as stats_file:
    print >> stats_file, r'\def\jhaliascount{%d}' % sum(aliases)
    print >> stats_file, r'\def\jhtotaltests{%d}' % len(aliases)
    print >> stats_file, r'\def\jhmaxalias{%d}' % sorted(aliases)[-1]
