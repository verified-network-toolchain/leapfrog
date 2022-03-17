#!/usr/bin/env python3

import argparse
from dataclasses import dataclass

from datetime import time, datetime, timedelta

import os
from os import path
from pathlib import Path
from typing import Tuple, Optional

import re

def fmt_td(td:timedelta): 
  s = int(td.total_seconds())
  hours, remainder = divmod(s, 3600)
  minutes, seconds = divmod(remainder, 60)
  return '{:02}:{:02}:{:02}'.format(int(hours), int(minutes), int(seconds))

@dataclass(frozen=True)
class LogData:
  name: str
  hash: str
  dt: time
  runtime: timedelta
  memory_use: int
  success: bool

  def to_csv_row(self):
    return ",".join([self.name, self.hash, str(self.dt), fmt_td(self.runtime), str(self.memory_use)]) + ("" if self.success else "*")


@dataclass(frozen=True)
class LogDataPartial:
  name: str
  runtime: timedelta
  memory_use: int
  success: bool

  def to_csv_row(self):
    return ",".join([self.name, fmt_td(self.runtime), str(self.memory_use)]) + ("" if self.success else "*")

def parse_stats(loc: str) -> Tuple[timedelta, int, bool] : 

  # re_runtime_valu = r"(\d\d:\d\d:\d\d)|(\d:\d\d\.\d\d)"

  re_runtime = r"\s*Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*((\d+:\d\d:\d\d)|(\d\d?:\d\d\.\d\d))\s*"
  runtime : Optional[timedelta] = None
  
  mem_bytes : Optional[int] = None
  re_mem = r"\s*Maximum resident set size \(kbytes\):\s*(\d+)\s*"

  success : Optional[bool] = None
  re_succ = r"\s*Exit status: (\d+)\s*"

  with open(loc) as f:
    for line in f:
      rt_match = re.match(re_runtime, line)
      mem_match = re.match(re_mem, line)
      succ_match = re.match(re_succ, line)
      if rt_match:
        _, long, short = rt_match.groups()
        if long:
          times = [int(x) for x in long.split(':')]
          hrs, mins, secs = times[0], times[1], times[2]
          runtime = timedelta(hours=hrs,minutes=mins,seconds=secs) 
        elif short: 
          mins, secs_str = short.split(':')[0], short.split(':')[1]
          secs, micros = secs_str.split('.')[0], secs_str.split('.')[1]
          micros = int(micros) * 10000
          runtime = timedelta(minutes=int(mins), seconds=int(secs), microseconds=micros)
        else:
          assert False
      elif mem_match:
        mem_bytes = int(mem_match.group(1))
      elif succ_match:
        # print('parsed success to')
        # print(succ_match.groups())
        result_val = int(succ_match.group(1))
        success = result_val == 0



  
  if runtime is None:
    print('could not parse runtime in', loc)
    assert False
  elif mem_bytes is None:
    print('could not parse memory in', loc)
    assert False
  elif success is None:
    print('could not parse output result', loc)
    assert False
  else:
    return (runtime, mem_bytes, success)


def import_log(location_path: str):
  pref, name = path.split(location_path)
  name = name.split('.')[0]
  
  pref, dt = path.split(pref)
  
  fmt = "%d-%m-%Y.%H:%M:%S"
  dt = datetime.strptime(dt, fmt)

  _, hash = path.split(pref)

  assert len(hash) == 7

  runtime, mem, success = parse_stats(location_path)

  return LogData(
      name = name
    , hash = hash
    , dt = dt
    , runtime = runtime
    , memory_use= mem
    , success=success
  )

def import_partial_log(name: str, location_path: str):
  runtime, mem, success = parse_stats(location_path)
  return LogDataPartial(name=name, runtime=runtime, memory_use=mem, success=success)


parser = argparse.ArgumentParser()
parser.add_argument('location', metavar="path", type=str, help="location of logs (a folder for multiple logs, a file for one log)")
parser.add_argument('--one-file', dest="file", default=False, action='store_const', const=True,
  help="parse just one log file"
)


if __name__ == "__main__":
  args = parser.parse_args()

  loc = args.location

  if args.file:
    try: 
      print(import_log(loc).to_csv_row())
    except: 
      print("couldn't parse hash/time, trying to partially parse...")
      try: 
        name = Path(loc).name
        print(import_partial_log(name, str(Path(loc).absolute())).to_csv_row())
      except:
        print("couldn't parse log at all:", str(Path(loc).name))
  else:
    root = Path(loc)
    for f in root.glob("*.out"):
      try:
        print(import_log(str(f.absolute())).to_csv_row())
      except: 
        print("couldn't parse hash/time, trying to partially parse...")
        try: 
          print(import_partial_log(f.name, str(f.absolute())).to_csv_row())
        except:
          print("couldn't parse log at all:", str(f.absolute()))



