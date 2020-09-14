#!python3

import os
import subprocess
import sys
import tempfile
import yaml
from yaml import FullLoader

this_dir = os.path.realpath(os.path.dirname(sys.argv[0]))

subprocess.check_call([os.path.join(this_dir, "gradlew"), "--console",
                       "plain", "installDist", "integrationJar"], cwd=this_dir)

integration = os.path.join(this_dir, "build/libs/integration.jar")
reg_script = os.path.join(this_dir, "regnant.py")

with tempfile.NamedTemporaryFile(delete=True) as t:
    subprocess.check_call([os.path.join(this_dir, "build/install/regnant/bin/generateWork"),
                           os.path.join(this_dir, "build/libs/integration.jar"), t.name])
    worklist = yaml.load(t, Loader=FullLoader)


for (k, v) in worklist.items():
    print("Testing", k)
    ret = subprocess.call([
        reg_script,
        "--jar=" + integration,
        "--skip-build",
        sys.argv[1], k
    ], stdout=subprocess.DEVNULL)
    if (ret != 0) != v:
        print("Unexpected result for", k)
        sys.exit(1)

print("DONE")
