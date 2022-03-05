from dataclasses import dataclass

@dataclass(frozen=True)
class LogConfig:
  location : str # location on disk for saving logs
