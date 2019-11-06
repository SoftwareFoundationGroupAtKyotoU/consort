import yaml
import shutil
import os
import sys

with open(sys.argv[1], 'r') as f:
    conf = yaml.load(f)

conf["jayhorn"] = None
conf["jayhorn_bench"]["jayhorn_imp"] = None

src_dir = os.path.dirname(sys.argv[1])

conf["consort_bench"]["java"] = "benchmarks/consort/java"

for p in ["pos", "neg"]:
    for t in conf["consort_bench"][p]:
        output_name = t["name"].lower() + ".imp"
        output_path = os.path.join("benchmarks/consort", output_name)
        shutil.move(os.path.join(src_dir, t["path"]), os.path.join(src_dir, output_path))
        t["path"] = output_path

with open(sys.argv[1], 'w') as r:
    yaml.dump(conf, r)
