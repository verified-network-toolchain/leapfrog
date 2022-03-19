#!/usr/bin/env python3

from sys import platform
from typing import Optional
from config.logs import *
from config.benchmarks import *

import git

from datetime import datetime

import os

import subprocess

from pathlib import Path

from tqdm import tqdm
from enum import Enum

import argparse
import resource
import pathlib

LEAPFROG_ROOT = pathlib.Path(__file__).parent.parent.resolve()

@dataclass(frozen=True)
class RunnerConfig:
  leapfrog_target: str # dependency of all benchmarks, needs to be run before timing
  time_cmd: str

runner_conf = RunnerConfig(
    leapfrog_target="build"
  , time_cmd= "gtime -v" if platform.startswith('darwin') else "/usr/bin/time -v"
  , 
)


def get_current_commit():
  repo = git.Repo(search_parent_directories=True)
  return repo.head.object

def get_current_short_hash():
  repo = git.Repo(search_parent_directories=True)
  sha = repo.head.commit.hexsha
  return repo.git.rev_parse(sha, short=7)

def make_bench_prefix(conf:LogConfig):
  now = datetime.now()
  fmt = "%d-%m-%Y.%H:%M:%S"
  
  return os.path.join(conf.location, get_current_short_hash(), now.strftime(fmt))


# assumes that the dependencies of the benchmark has been already built
def run_benchmark(prefix: str, time_cmd: str, b: Benchmark):
  
  targ = b.target
  location = Path(os.path.join(prefix, "%s.out" % b.name))
  print('output log is in',location)

  location.touch()

  with location.open('a') as f:
    subprocess.run("%s make %s" % (time_cmd, targ), cwd="..", shell=True, stdout=f, stderr=subprocess.STDOUT)


MainOpt = Enum('MainOpt', 'SMALL LARGE ALL ONE')


def main(opt: MainOpt, log_config, bench_name : Optional[str] = None):

  benches : Benchmarks
  if opt == MainOpt.SMALL:
    print("running small benchmarks")
    benches = small_benchmarks
  elif opt == MainOpt.LARGE:
    print("running large benchmarks")
    benches = large_benchmarks
  elif opt == MainOpt.ALL:
    print("running all benchmarks")
    benches = all_benchmarks
  elif opt == MainOpt.ONE:
    if bench_name:
      print('running one benchmark:', bench_name)
      benches = all_benchmarks.filter_by_name(bench_name)
    else:
      print('missing required benchmark argument for size one')
      assert False
  else:
    print('bad argument to main', opt)
    assert False
 
  prefix = make_bench_prefix(log_config)

  os.makedirs(prefix, mode=0o777)

  print("building leapfrog...")
  try:
    subprocess.run("make -j %s" % runner_conf.leapfrog_target, cwd="..", shell=True, check=True)
    print("done!")

    print("starting benchmarking with output directory:", prefix)

    for bench in tqdm(benches.benchmarks):
      print('running benchmark for', bench.name)
      try: 
        run_benchmark(prefix, runner_conf.time_cmd, bench)
        print('done!')
      except: 
        print('hit an error in ', bench.name)
        print('continuing anyway...')
  except Exception as e:
    print("ran into error while running benchmarks, cleaning up...")
    subprocess.run("make clean", cwd="..", shell=True)
    print("done!")
    raise e

  
parser = argparse.ArgumentParser()
parser.add_argument('--size', choices=['small', 'large', 'all', 'one'], required=True)
parser.add_argument('--log-dir', default=os.path.join(LEAPFROG_ROOT,
"benchmarking/logs"))
parser.add_argument('-f', default=None, choices=[ 
    "ethernet" , "selfcomparison" , "mpls" , "sloppystrict_filter" , "sloppystrict_stores",
    "ipfilter" , "edgeself" , "edgetrans" , "datacenter" , 
    "serviceprovider" , "enterprise" , "ipoptions2"
  ],
  help="benchmark name if size is one"
)

if __name__ == "__main__":
  args = parser.parse_args()
  bench_name = None
  opt : MainOpt
  if args.size == 'small':
    opt = MainOpt.SMALL
  elif args.size == 'large':
    curr_limit, _ = resource.getrlimit(resource.RLIMIT_STACK)
    if not curr_limit == resource.RLIM_INFINITY:
      print("warning: running large benchmarks without using unlimited stack size")
      print("try rerunning with ulimit -s unlimited")
    opt = MainOpt.LARGE
  elif args.size == 'all':
    curr_limit, _ = resource.getrlimit(resource.RLIMIT_STACK)
    if not curr_limit == resource.RLIM_INFINITY:
      print("warning: running large benchmarks without using unlimited stack size")
      print("try rerunning with ulimit -s unlimited")
    opt = MainOpt.ALL
  elif args.size == 'one':
    opt = MainOpt.ONE
    bench_name = args.f
  else:
    print('bad CLI argument to runner', args.size)
    assert False
  log_config = LogConfig(args.log_dir)
  main(opt, log_config, bench_name=bench_name)
