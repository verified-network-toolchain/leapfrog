from dataclasses import dataclass

@dataclass(frozen=True)
class Benchmark:
  name : str # name of benchmark
  target : str # makefile target of benchmark

@dataclass(frozen=True)
class Benchmarks:
  benchmarks: list[Benchmark] # all benchmarks

  def __add__(self, other): 
    Benchmarks(benchmarks=self.benchmarks + other.benchmarks)


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
      Benchmark(name="ipoptions3", target="ipoptions3")
    , Benchmark(name="edgeself", target="edgeself")
    , Benchmark(name="edgetrans", target="edgetrans")
    , Benchmark(name="datacenter", target="datacenterself")
    , Benchmark(name="serviceprovider", target="serviceproviderself")
    , Benchmark(name="enterprise", target="enterpriseself")
  ]
)

all_benchmarks : Benchmarks = small_benchmarks + large_benchmarks
