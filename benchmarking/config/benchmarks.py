from dataclasses import dataclass

@dataclass(frozen=True)
class Benchmark:
  name : str # name of benchmark
  target : str # makefile target of benchmark

@dataclass(frozen=True)
class Benchmarks:
  benchmarks: list[Benchmark] # all benchmarks

  def __add__(self, other): 
    if isinstance(other, Benchmarks):
      return Benchmarks(benchmarks=self.benchmarks + other.benchmarks)
    else:
      assert False

  def filter_by_name(self, name: str):
    return Benchmarks(benchmarks=[x for x in self.benchmarks if x.name == name])

# To modify benchmarks, change the list of benchmarks below by adding/editing rows

small_benchmarks : Benchmarks = Benchmarks(
  benchmarks=[
    	Benchmark(name="ethernet", target="ethernet")
    , Benchmark(name="selfcomparison", target="selfcomparison")
    , Benchmark(name="mpls", target="mpls")
    , Benchmark(name="sloppystrict", target="sloppystrict")
    , Benchmark(name="ipfilter", target="ipfilter")
  ]
)

large_benchmarks : Benchmarks = Benchmarks(
  benchmarks=[
      Benchmark(name="edgeself", target="edgeself")
    , Benchmark(name="edgetrans", target="edgetrans")
    , Benchmark(name="datacenter", target="datacenterself")
    , Benchmark(name="serviceprovider", target="serviceproviderself")
    , Benchmark(name="enterprise", target="enterpriseself")
    , Benchmark(name="ipoptions2", target="ipoptions2")
  ]
)

all_benchmarks : Benchmarks = small_benchmarks + large_benchmarks
