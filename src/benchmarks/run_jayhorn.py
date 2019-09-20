import os, subprocess, sys

def has_fail_tag(f_name):
    with open(f_name, 'r') as f:
        first_line = f.readline()
        return first_line.startswith("/** fail")

this_dir = os.path.dirname(sys.argv[0])
test_suite = os.path.join(this_dir, "..", "_build", "default", "test_suite.exe")

# filter out the fail tests
all_args = []
rest_parse = False
for arg in sys.argv[1:]:
    if not rest_parse:
        if arg.endswith(".imp"):
            rest_parse = True
            all_args.append("-files")
        else:
            all_args.append(arg)
    if rest_parse and not has_fail_tag(arg):
        all_args.append(arg)    

ret = subprocess.call([ test_suite ] + all_args)
sys.exit(ret)

