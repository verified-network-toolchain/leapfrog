#!/usr/bin/env python3

import argparse
from dataclasses import dataclass

from datetime import time, datetime

import os
from os import path
from pathlib import Path
from typing import Tuple, Optional

import re

@dataclass(frozen=True)
class LogData:
  name: str
  hash: str
  dt: datetime
  runtime: time
  memory_use: int

  def to_csv_row(self):
    return ",".join([self.name, self.hash, str(self.dt), str(self.runtime), str(self.memory_use)])


@dataclass(frozen=True)
class LogDataPartial:
  name: str
  runtime: time
  memory_use: int

  def to_csv_row(self):
    return ",".join([self.name, str(self.runtime), str(self.memory_use)])


def parse_stats(loc: str) -> Tuple[time, int] : 

  # re_runtime_valu = r"(\d\d:\d\d:\d\d)|(\d:\d\d\.\d\d)"

  re_runtime = r"\s*Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*((\d+:\d\d:\d\d)|(\d:\d\d\.\d\d))\s*"
  runtime : Optional[time] = None
  
  mem_bytes : Optional[int] = None
  re_mem = r"\s*Maximum resident set size \(kbytes\):\s*(\d+)\s*"

  with open(loc) as f:
    for line in f:
      rt_match = re.match(re_runtime, line)
      mem_match = re.match(re_mem, line)
      if rt_match:
        _, long, short = rt_match.groups()
        if long:
          # the time is ISO, we can use a default parser
          runtime = time.fromisoformat(long)
        elif short: 
          # ugh, we have to manually parse the fractional seconds to microseconds...
          mins, secs_str = short.split(':')[0], short.split(':')[1]
          secs, micros = secs_str.split('.')[0], secs_str.split('.')[1]
          micros = int(micros) * 10000
          runtime = time(minute=int(mins), second=int(secs), microsecond=micros)
        else:
          assert False
      elif mem_match:
        mem_bytes = int(mem_match.group(1))
  
  if runtime is None:
    print('could not parse runtime in', loc)
    assert False
  elif mem_bytes is None:
    print('cloudl not parse memory in', loc)
    assert False
  else:
    return (runtime, mem_bytes)


def import_log(location_path: str):
  pref, name = path.split(location_path)
  name = name.split('.')[0]
  
  pref, dt = path.split(pref)
  
  fmt = "%d-%m-%Y.%H:%M:%S"
  dt = datetime.strptime(dt, fmt)

  _, hash = path.split(pref)

  assert len(hash) == 7

  runtime, mem = parse_stats(location_path)

  return LogData(
      name = name
    , hash = hash
    , dt = dt
    , runtime = runtime
    , memory_use= mem
  )

def import_partial_log(name: str, location_path: str):
  runtime, mem = parse_stats(location_path)
  return LogDataPartial(name=name, runtime=runtime, memory_use=mem)


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
        print("couldn't parse log at all:", str(Path(loc)))
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
          print("couldn't parse log at all:", str(Path(loc)))



