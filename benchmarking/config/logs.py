from dataclasses import dataclass

@dataclass(frozen=True)
class LogConfig:
  location : str # location on disk for saving logs

  # def validate():
    
# To change the logging location, substitute in a new string for the location argument
log_config : LogConfig = LogConfig(
  location="/Users/john/leapfrog/benchmarking/logs/"
)
