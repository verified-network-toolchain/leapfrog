from __future__ import annotations
from dataclasses import dataclass
import dataclasses
import enum
from typing import Match, Optional, Pattern

import re

def preamble () :
  return """\
Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.BisimChecker.

Require Import Poulet4.P4automata.Notations.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.
"""

def hdr_ty_decl(widths: dict[str, int]):
  output = "Inductive header : nat -> Type :="
  for h, w in widths.items():
    output += f"\n| {h}: header {w}"
  return output + ".\n"

def state_ty_decl(states: list[str]):
  return "Inductive state := " + " ".join([f"| {s}" for s in states]) + ".\n"

def format_one_width(hdrs: list[str], widths: dict[str, int], width: int):
  hdrs = [x for x in hdrs if widths[x] == width]
  match = f"Definition h{width}_eq_dec (x y: header {width}) : {{x = y}} + {{x <> y}}.\n"
  match += "refine (\n"
  match += "  match x with\n"
  for outer in hdrs:
    match += f"  | {outer} => \n"
    match += "    match y with\n"
    for inner in hdrs:
      match += f"    | {inner} => "
      if outer == inner:
        match += "left eq_refl\n"
      else:
        match += "right _\n"
    match += "    end\n"
  match += "  end\n"
  match += "); unfold \"<>\"; intros H; inversion H.\n"
  match += "Defined.\n"

  return match

  # Definition h8_eq_dec (x y: header 8) : {x = y} + {x <> y}. 
  # refine (
  #   match x with 
  #   | Typ => 
  #     match y with 
  #     | Typ => left eq_refl
  #     | Len => right _
  #     | Scratch8 => right _
  #     end
  #   | Len => 
  #     match y with 
  #     | Typ => right _
  #     | Len => left eq_refl
  #     | Scratch8 => right _
  #     end
  #   | Scratch8 => 
  #       match y with 
  #       | Typ => right _
  #       | Len => right _
  #       | Scratch8 => left eq_refl
  #       end
  #   end
  # ); unfold "<>"; intros H; inversion H.
  # Defined.


  # Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  #   solve_header_eqdec_ n x y 
  #     ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h8_eq_dec) :: 
  #       (existT _ _ h16_eq_dec) :: (existT _ _ h24_eq_dec) :: (existT _ _ h32_eq_dec) :: 
  #       (existT _ _ h40_eq_dec) :: (existT _ _ h48_eq_dec) :: nil).
  # Defined. 

def format_header_eqdec (widths: dict[str, int]):
  widths_ = list(set(widths.values()))
  output = "Derive Signature for header.\nDefinition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.\n"
  output += "  solve_header_eqdec_ n x y\n"
  output += f"    ((existT (fun n => forall x y: header n, {{x = y}} + {{x <> y}}) _ h{widths_[0]}_eq_dec) ::\n"
  for w in widths_[1:]:
    output += f"     (existT _ _ h{w}_eq_dec) ::\n"
  output += "      nil).\n"
  output += "Defined.\n\n"
  output += "Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.\n"

  output += "Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.\n"
  output += "  solve_eqdec'.\n"
  output += "Defined.\n"
  return output

def format_header_finite(hdrs: list[str], widths: dict[str, int]):
  output = "Global Instance header_finite: forall n, @Finite (header n) _ _.\n"
  output += "  intros n; solve_indexed_finiteness n ["
  widths_ = list(set(widths.values()))
  output += f"{widths_[0]}"
  for w in widths_[1:]:
    output += f"; {w} "
  output += "].\nQed.\n\n"

  output += "Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=\n"
  output += "  {| enum := [ \n"
  output += f"      existT _ _ {hdrs[0]}\n"
  for h in hdrs[1:]:
    output += f"    ; existT _ _ {h}\n"
  output += "    ] |}.\n"
  output += "Next Obligation.\n  solve_header_finite.\nQed.\nNext Obligation.\n"
  output += "dependent destruction X; subst; \n"
  output += "repeat (\n"
  output += "  match goal with \n"
  output += "  | |- ?L \/ ?R => (now left; trivial) || right\n"
  output += "  end\n).\nQed.\n"  

  return output


def format_headers (hdrs: list[str], widths:dict[str, int]):

  output = hdr_ty_decl(widths)

  widths_ = set(widths.values())

  for w in widths_:
    output += format_one_width(hdrs, widths, w)
  
  output += format_header_eqdec(widths)
  output += format_header_finite(hdrs, widths)

  return output

def format_states (states: list[str]):
  output = state_ty_decl(states)
  output += f"\
Scheme Equality for state.\n\
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.\n\
Global Program Instance state_finite: @Finite state _ state_eq_dec :=\n\
  {{| enum := [{states[0]}"
  for s in states[1:]:
    output += f"; {s}"
  output += f"] |}}.\n"
  output += f"\
Next Obligation.\n\
repeat constructor;\n\
  repeat match goal with\n\
          | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H\n\
          | |- ~ List.In _ [] => apply List.in_nil\n\
          | |- ~ List.In _ (_ :: _) => unfold not; intros\n\
          | H: List.In _ (_::_) |- _ => inversion H; clear H\n\
          | _ => discriminate\n\
          end.\n\
Qed.\n\
Next Obligation.\n\
  destruct x; intuition congruence.\n\
Qed.\n"

  return output


class tcam_mask(enum.Enum):
  BIT = 0
  # BYTE = 1
  WILD = 1

  @property
  def width(self):
    match self:
      case tcam_mask.BIT: return 1
      # case tcam_mask.BYTE: return 4
      case tcam_mask.WILD: return 1
  
  def __or__(self, other: tcam_mask):
    match self, other:
      case tcam_mask.WILD, _: return tcam_mask.WILD
      case _, tcam_mask.WILD: return tcam_mask.WILD
      case _, _:
        if self == other:
          return self
        else:
          print("can't OR together bit and byte masks:", self, other)
          assert False


def c_to_mask(c: chr) -> tcam_mask:
  match c: 
    # case 'f': return tcam_mask.BYTE
    case '1': return tcam_mask.BIT
    case '0': return tcam_mask.WILD
    case _: 
      print("unhandled mask:", c)
      assert False

def s_to_masks(s: str) -> list[tcam_mask]:
  return [c_to_mask(x) for x in s]

def hexs_to_masks(s: str, width: int = 4) -> list[tcam_mask]:
  binary_byte = bin(int(s, base=16))
  # Use zfill to pad the string with zeroes as we want all 8 digits of the byte.
  return [s_to_masks(x) for x in binary_byte[2:].zfill(width)]

def hexp_to_digs(s: str, width: int = 0) -> list[bool]:
  if not width:
    width = len(s)*4
  return [bool(int(c)) for c in bin(int(s, base=16))[2:].zfill(width)]



  
@dataclass
class tcam_transition:
  masks: list[tcam_mask]
  pats: list[str]
  next_state: int | bool
  next_extract: int

# @dataclass 
# class tcam_window:
#   offset: int # in nibbles
#   width: int

@dataclass
class tcam_state:
  windows: list[int]
  transitions: list[tcam_transition]

  # in bytes
  @property
  def window(self):
    return max(self.windows) + 2

@dataclass
class tcam_program:
  window_size: int
  states: list[tcam_state]


def header_sizes_state(st: tcam_state) -> set[int]:
  
  window_size = st.window*8
  ret = {window_size} | {trans.next_extract*8 - window_size for trans in st.transitions}
  return {x for x in ret if x > 0}

def header_sizes_prog(p: tcam_program) -> set[int]:
  ret = set()
  for st in p.states:
    ret |= header_sizes_state(st)
  return ret

def state_names_state(pref: int, st: tcam_state) -> set[str]:
  
  output = {f"State_{pref}"}

  for i, trans in enumerate(st.transitions):
    nxt_extract = trans.next_extract*8 - st.window*8
    if nxt_extract > 0:
      output.add(f"State_{pref}_suff_{i}")
  return output

def state_names_prog(p: tcam_program) -> set[str]:
  output = set()
  for i, st in enumerate(p.states):
    output |= state_names_state(i, st)
  return output

def format_tcam_state(pref: int, st: tcam_state):

  output = f"  | State_{pref} => {{|\n"

  bits = st.window*8

  window_var = f"buf_{bits}"
  output += f"    st_op := extract({window_var});\n"

  slices = [f"[{w*8 + off} -- {w*8 + off}]" for w in st.windows for off in range(16)]

  output += f"    st_trans := transition select (| " + ", ".join([f"(EHdr {window_var}){x}" for x in slices]) + f"|) {{{{\n"
  
  suffs = []

  for i, trans in enumerate(st.transitions):

    masks_str = ""
    for j, mask in enumerate(trans.masks):
      # print("pat:", trans.pats[j])
      print("mask:", mask, mask == tcam_mask.WILD, mask == tcam_mask.BIT)
      match mask:
        case tcam_mask.WILD: 
          if masks_str == "":
            masks_str = "*"
          else:
            masks_str += f", *"
        # case tcam_mask.BYTE:
        #   if masks_str == "":
        #     masks_str = "hexact 0x" + "".join(trans.pats[j])
        #   else:
        #     masks_str += f", hexact 0x{''.join(trans.pats[j])}"
        case tcam_mask.BIT:
          # dig = "true" if trans.pats[j] == "1" else "false"
          dig = trans.pats[j]
          if masks_str == "":
            masks_str = f"exact #b|{dig}"
          else:
            masks_str += f", exact #b|{dig}"

    nxt_extract = trans.next_extract*8 - st.window*8
    output += f"      [| {masks_str} |] ==> "

    if nxt_extract == 0:
      output += "accept"
    elif nxt_extract < 0:
      output += "reject"
    else:
      suffs.append((i, nxt_extract, trans.next_state))
      output += f"inl State_{pref}_suff_{i}"
    output += " ;;;\n"
  
  output += "      reject\n"
  output += f"    }}}}\n"
  output += f"  |}}\n"
  
  return (output, suffs)


  
def format_tcam_trailer(pref: int, suffs: list[tuple[int, int, int|bool]]):
  output = ""
  for i, width, nxt in suffs:
    output += f"  | State_{pref}_suff_{i} => {{|\n"
    output += f"    st_op := extract(buf_{width});\n"
    output += f"    st_trans := transition "
    if type(nxt) == bool:
      if nxt:
        output += "accept"
      else:
        output += "reject"
    else:
      output += f"inl State_{i}"
    
    output += ";\n"
    output += f"  |}}\n"
  return output

def format_tcam_prog(tcp: tcam_program):
  hdr_sizes = header_sizes_prog(tcp)
  hdr_widths = {f"buf_{x}":x for x in hdr_sizes}
  hdr_names = list(hdr_widths.keys())

  state_names = list(state_names_prog(tcp))


  output = preamble() + format_states(state_names) + format_headers(hdr_names, hdr_widths) 

  output += "Definition states (s: state) :=\n"
  output += "  match s with\n"

  for i, state in enumerate(tcp.states):
    trans_str, trailers = format_tcam_state(i, state)
    trailer_str = format_tcam_trailer(i, trailers)
    output += trans_str
    output += trailer_str
  
  output += """\
end.
Program Definition aut: Syntax.t state header :=
  {| t_states := states |}.
Solve Obligations with (destruct s; cbv; Lia.lia).
  """
  return output

def print_tcam_prog(tcp: tcam_program):
  print(format_tcam_prog(tcp))


ex_small_prog = tcam_program( window_size=2, states=[
  tcam_state(windows = [
      2
  ], transitions=[tcam_transition(
    masks=[msk for x in "ff" for msks in hexs_to_masks(str(x)) for msk in msks],
    pats=["1" if d else "0" for d in hexp_to_digs("08")],
    next_state=True,
    next_extract=34
  )])
])

#   First-Lookup: [0, 12]
#   Match: ([ff, 00, 00, ff, ff], [00, 00, 00, 08, 00])   Next-State: 255/255   Adv:  34   Next-Lookup: [0, 0]   Hdr-Starts: [( 0, 1, 14), (14, 4,  0), ( 0, 0,  0)]     
#   Match: ([ff, 00, 00, ff, ff], [00, 00, 00, 81, 00])   Next-State:   1/255   Adv:  16   Next-Lookup: [0, 4]   Hdr-Starts: [( 0, 1, 14), (14, 2,  4), ( 0, 0,  0)]     
#   Match: ([ff, 00, 00, 00, 00], [00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  14   Next-Lookup: [0, 0]   Hdr-Starts: [( 0, 1, 14), ( 0, 0,  0), ( 0, 0,  0)]     
ex0_transitions = [
  tcam_transition(
    masks=[msk for x in "0000ffff" for msks in hexs_to_masks(x) for msk in msks],
    pats=["1" if d else "0" for d in hexp_to_digs("00000800")],
    next_state=True,
    next_extract=34
  ),
  tcam_transition(
    masks=[msk for x in "0000ffff" for msks in hexs_to_masks(x) for msk in msks],
    pats=["1" if d else "0" for d in hexp_to_digs("00008100")],
    next_state=1,
    next_extract=16
  ),
  # tcam_transition(
  #   masks=[tcam_mask(None), tcam_mask(None), tcam_mask(None), tcam_mask(None)],
  #   pats=["00", "00", "00", "00"],
  #   next_state=True,
  #   next_extract=14
  # )
]

#   Match: ([ff, ff, ff,00, 00], [01, 08, 00, 00, 00])   Next-State: 255/255   Adv:  22   Next-Lookup: [0, 0]   Hdr-Starts: [( 2, 4,  0), ( 0, 0,  0), ( 0, 0,  0)]     
#   Match: ([ff, ff, ff, ff, ff], [01, 81, 00, 08, 00])   Next-State: 255/255   Adv:  26   Next-Lookup: [0, 0]   Hdr-Starts: [( 2, 3,  4), ( 6, 4,  0), ( 0, 0,  0)]     
#   Match: ([ff, ff, ff, 00, 00], [01, 81, 00, 00, 00])   Next-State: 255/255   Adv:   6   Next-Lookup: [0, 0]   Hdr-Starts: [( 2, 3,  4), ( 0, 0,  0), ( 0, 0,  0)]     
#   Match: ([ff, 00, 00, 00, 00], [01, 00, 00, 00, 00])   Next-State: 255/255   Adv:   2   Next-Lookup: [0, 0]   Hdr-Starts: [( 0, 0,  0), ( 0, 0,  0), ( 0, 0,  0)]     
ex1_transitions = [
  tcam_transition(
    masks=[msk for x in "ffff0000" for msks in hexs_to_masks(x) for msk in msks],
    pats=["1" if d else "0" for d in hexp_to_digs("08000000")],
    next_state=True,
    next_extract=22
  ),
  tcam_transition(
    masks=[msk for x in "ffffffff" for msks in hexs_to_masks(x) for msk in msks],
    pats=["1" if d else "0" for d in hexp_to_digs("81000800")],
    next_state=True,
    next_extract=26
  ),
  # tcam_transition(
  #   masks=[tcam_mask("ff"), tcam_mask("ff"), tcam_mask(None), tcam_mask(None)],
  #   pats=["8100", "00", "00"],
  #   next_state=True,
  #   next_extract=6
  # ),
  # tcam_transition(
  #   masks=[tcam_mask(None), tcam_mask(None), tcam_mask(None), tcam_mask(None)],
  #   pats=["00", "00", "00", "00"],
  #   next_state=True, # not sure on this one
  #   next_extract=2
  # )
]

ex_prog = tcam_program(window_size=2, states=[
  tcam_state(
    windows=[
      0, 12
    ],
    transitions=ex0_transitions),
  tcam_state(
    windows=[
      0, 12
    ], transitions=ex1_transitions)
])

def get_prefix(r: Pattern, s:str) -> Optional[tuple[Match, str]]:
  it = r.match(s)
  if it:
    return (it, s.removeprefix(it.group(0)))

@dataclass
class trans_data:
  state: int
  lookups: list[int]

def parse_trans (s: str) -> tuple[trans_data, tcam_transition]:

  pref_re = re.compile("\s*Match:\s*(\(.*?\))\s*")
  # Match: ([ff, ff, ff,00, 00], [01, 08, 00, 00, 00])   Next-State: 255/255   Adv:  22   Next-Lookup: [0, 0]   Hdr-Starts: [( 2, 4,  0), ( 0, 0,  0), ( 0, 0,  0)]  
  pref_m, suff = get_prefix(pref_re, s)
  match_re = re.compile("\(\[([0-9a-f][0-9a-f](,\s*[0-9a-f][0-9a-f])*)\],\s*\[([0-9a-f][0-9a-f](,\s*[0-9a-f][0-9a-f])*)\]\)")
  
  match_m = match_re.match(pref_m.group(1))

  # print("after first match:", match_m.group(1))

  masks_raw = match_m.group(1).split(',')
  pats_raw = match_m.group(3).split(',')
  width = 8
  trans_masks = [x for it in masks_raw[1:] for x in hexs_to_masks(it.strip(), width)]
  trans_pats = [c for x in pats_raw for c in bin(int(x.strip(), base=16))[2:].zfill(width)]

  state = int(trans_pats[0:8])

  assert len(trans_masks) == len(trans_pats[8:])

  nxt_state_re = re.compile("\s*Next-State:\s*(\d+)/(\d+)")
  nxt_match, suff = get_prefix(nxt_state_re, suff)
  num, denom = int(nxt_match.group(1)), int(nxt_match.group(2))
  nxt_state : int | bool = num
  if num == denom:
    nxt_state = True
  
  advance_re = re.compile("\s*Adv:\s*(\d+)")
  adv_match, suff = get_prefix(advance_re, suff)

  next_extract = int(adv_match.group(1))

  nxt_lookup = re.compile("\s*Next-Lookup:\s*\[(.*?)\]")
  nxt_look_match, _ = get_prefix(nxt_lookup, suff)

  lookups = [int(x.strip()) for x in nxt_look_match.group(1).split(",")]

  return (trans_data(state, lookups), tcam_transition(masks=trans_masks, pats=trans_pats[8:], next_state=nxt_state, next_extract=next_extract))

def parse_first_lookup(s: str) -> list[int]:
  # First-Lookup: [0, 12, 0, 0]

  matcher = re.compile(".*?\[(.*?)\].*")

  return [int(x.strip()) for x in matcher.match(s).group(1).split(',')]

def parse_prog(s: str):
  # parse each line as a transition
  lines = s.splitlines()
  first_lookup = parse_first_lookup(lines[0])
  trans_dater = [parse_trans(x) for x in lines[1:]]

  # map states to lookups
  states_lookups: dict[int, list[list[int]]] = {t_data.state: [] for t_data, _ in trans_dater}

  for t_data, trans in trans_dater:
    if type(trans.next_state) == int:
      states_lookups[trans.next_state].append(t_data.lookups)



 # toss them into a dictionary keyed by state id
  states: dict[int, list[tcam_transition]] = {t_data.state: [] for t_data, _ in trans_dater}

  for state in states.keys():
    lookupss = states_lookups[state]
    for lookup in lookupss[1:]:
      assert lookup == lookupss[0]

  for t_data, trans in trans_dater:
    states[t_data.state].append(trans)

  state_ids = list(states.keys())
  state_ids.sort()

  prog_states = []
  for id in state_ids:
    lookups = first_lookup
    if not id == 0:
      lookups = states_lookups[id][0]
      
   
    state_masks = [tcam_mask.WILD] * len(lookups) * 4
    for trans in states[id]:

      for i, mask in enumerate(trans.masks):
        print("masks and lookups len", len(trans.masks), len(lookups))
        state_masks[i] |= mask
    
    offsets = [x for y in lookups for x in [y*2, y*2+1]]

    windows = [tcam_window(offset=offsets[i], width=state_masks[i].width) for i in range(len(offsets))]
        
    state = tcam_state(windows=windows, transitions=states[id])
    prog_states.append(state)
  
  prog = tcam_program(window_size=2, states=prog_states)
  
  print("prog:", prog)

  return prog
  
test_prog_str = """\
First-Lookup: [0, 12, 0, 0]
  Match: ([ff, 00, 00, 00, 00, 00, 00, 00, 00], [01, 00, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  18   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 4,  0), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[eompls+ethernet2-1 (l:18) 0:17/17], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 00, 00, ff, ff, 00, 00, 00, 00], [00, 00, 00, 08, 00, 00, 00, 00, 00])   Next-State:   3/255   Adv:  14   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 1, 14), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [ipv4-bar0-1 (l:0) 0:--/--], done=False, patterns=1]   Nxt-State: 3
  Match: ([ff, 00, 00, ff, ff, 00, 00, 00, 00], [00, 00, 00, 86, dd, 00, 00, 00, 00])   Next-State: 255/255   Adv:  54   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 1, 14), (14, 5, 37), ( 0, 0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [ipv6-1 (l:40) 0:39/39], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 00, 00, ff, ff, 00, 00, 00, 00], [00, 00, 00, 88, 47, 00, 00, 00, 00])   Next-State:   4/255   Adv:  16   Next-Lookup: [0, 2, 4, 6]   Hdr-Starts: [( 0, 1, 14), (14, 2,  4), ( 0, 0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [mpls-1 (l:4) 0:1/1], done=False, patterns=2]   Nxt-State: 4
  Match: ([ff, 00, 00, ff, ff, 00, 00, 00, 00], [00, 00, 00, 88, 48, 00, 00, 00, 00])   Next-State:   4/255   Adv:  16   Next-Lookup: [0, 2, 4, 6]   Hdr-Starts: [( 0, 1, 14), (14, 2,  4), ( 0, 0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [mpls-1 (l:4) 0:1/1], done=False, patterns=2]   Nxt-State: 4
  Match: ([ff, 00, 00, 00, 00, 00, 00, 00, 00], [00, 00, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  14   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 1, 14), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 0f, 00, 00, 00, 00, 00, 00, 00], [03, 05, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  20   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 6, 12), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l0-1 (l:0) 0:--/--], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 0f, 00, 00, 00, 00, 00, 00, 00], [03, 06, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  24   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 6, 12), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l4-1 (l:4) 0:3/3], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 0f, 00, 00, 00, 00, 00, 00, 00], [03, 07, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  28   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 6, 12), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l8-1 (l:8) 0:7/7], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 0f, 00, 00, 00, 00, 00, 00, 00], [03, 08, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  32   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 6, 12), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l12-1 (l:12) 0:11/11], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 00, 00, 00, 00, 00, 00, 00, 00], [02, 00, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:  40   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 5, 37), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[ipv6-1 (l:40) 0:39/39], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 01, 00, 00, 00, 01, 00, f0, 00], [04, 00, 00, 00, 00, 01, 00, 00, 00])   Next-State:   1/255   Adv:   6   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 2, 3,  4), ( 6, 4,  0), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4] -> [mpls-2 (l:4) 0:3/4] -> [eompls+ethernet2-1 (l:18) 0:--/--], done=False, patterns=1]   Nxt-State: 1
  Match: ([ff, 01, 00, 00, 00, 01, 00, f0, 00], [04, 00, 00, 00, 00, 01, 00, 40, 00])   Next-State:   3/255   Adv:   6   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 2, 3,  4), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4] -> [mpls-2 (l:4) 0:3/4] -> [ipv4-bar0-1 (l:0) 0:--/--], done=False, patterns=1]   Nxt-State: 3
  Match: ([ff, 01, 00, 00, 00, 01, 00, f0, 00], [04, 00, 00, 00, 00, 01, 00, 60, 00])   Next-State:   2/255   Adv:   6   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 2, 3,  4), ( 6, 5, 37), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4] -> [mpls-2 (l:4) 0:3/4] -> [ipv6-1 (l:40) 0:--/--], done=False, patterns=1]   Nxt-State: 2
  Match: ([ff, 01, 00, 00, 00, 00, 00, 00, 00], [04, 00, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:   6   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 2, 3,  4), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4] -> [mpls-2 (l:4) 0:3/4], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 01, 00, f0, 00, 00, 00, 00, 00], [04, 01, 00, 00, 00, 00, 00, 00, 00])   Next-State:   1/255   Adv:   2   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 2, 4,  0), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4] -> [eompls+ethernet2-1 (l:18) 0:--/--], done=False, patterns=1]   Nxt-State: 1
  Match: ([ff, 01, 00, f0, 00, 00, 00, 00, 00], [04, 01, 00, 40, 00, 00, 00, 00, 00])   Next-State:   3/255   Adv:   2   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 0,  0), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4] -> [ipv4-bar0-1 (l:0) 0:--/--], done=False, patterns=1]   Nxt-State: 3
  Match: ([ff, 01, 00, f0, 00, 00, 00, 00, 00], [04, 01, 00, 60, 00, 00, 00, 00, 00])   Next-State:   2/255   Adv:   2   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 2, 5, 37), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4] -> [ipv6-1 (l:40) 0:--/--], done=False, patterns=1]   Nxt-State: 2
  Match: ([ff, 00, 00, 00, 00, 00, 00, 00, 00], [04, 00, 00, 00, 00, 00, 00, 00, 00])   Next-State: 255/255   Adv:   2   Next-Lookup: [0, 0, 0, 0]   Hdr-Starts: [( 0, 0,  0), ( 0, 0,  0), ( 0, 0,  0)]     # Match: [[mpls-1 (l:4) 2:3/4], done=True, patterns=1]   Nxt-State: 255
"""

service_provider = """\
First-Lookup: [0, 12]
  Match: ([ff, 00, 00, ff, ff], [00, 00, 00, 08, 00])   Next-State:   1/255   Adv:  14   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  1, 14), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [ipv4-bar0-1 (l:0) 0:--/--], done=False, patterns=1]   Nxt-State: 1
  Match: ([ff, 00, 00, ff, ff], [00, 00, 00, 86, dd])   Next-State: 255/255   Adv:  54   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  1, 14), (14,  8, 37), ( 0,  0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [ipv6-1 (l:40) 0:39/39], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 00, 00, ff, ff], [00, 00, 00, 88, 47])   Next-State:   4/255   Adv:  16   Next-Lookup: [0, 4]   Hdr-Starts: [( 0,  1, 14), (14,  2,  4), ( 0,  0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [mpls-1 (l:4) 0:1/1], done=False, patterns=2]   Nxt-State: 4
  Match: ([ff, 00, 00, ff, ff], [00, 00, 00, 88, 48])   Next-State:   4/255   Adv:  16   Next-Lookup: [0, 4]   Hdr-Starts: [( 0,  1, 14), (14,  2,  4), ( 0,  0,  0)]     # Match: [[ethernet-1 (l:14) 0:13/13] -> [mpls-1 (l:4) 0:1/1], done=False, patterns=2]   Nxt-State: 4
  Match: ([ff, 0f, 00, 00, 00], [01, 05, 00, 00, 00])   Next-State: 255/255   Adv:  20   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  9, 12), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l0-1 (l:0) 0:--/--], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 0f, 00, 00, 00], [01, 06, 00, 00, 00])   Next-State: 255/255   Adv:  24   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  9, 12), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l4-1 (l:4) 0:3/3], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 0f, 00, 00, 00], [01, 07, 00, 00, 00])   Next-State: 255/255   Adv:  28   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  9, 12), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l8-1 (l:8) 0:7/7], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 0f, 00, 00, 00], [01, 08, 00, 00, 00])   Next-State: 255/255   Adv:  32   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  9, 12), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[ipv4-1 (l:20) 0:19/19] -> [ipv4-pad-l12-1 (l:12) 0:11/11], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, 00, 00, 00, 00], [02, 00, 00, 00, 00])   Next-State: 255/255   Adv:  40   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  8, 37), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[ipv6-1 (l:40) 0:39/39], done=True, patterns=1]   Nxt-State: 255
  Match: ([ff, f0, 00, 00, 00], [03, 40, 00, 00, 00])   Next-State:   1/255   Adv:   0   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  7,  0), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[mpls-pseudo-1 (l:0) 0:--/0] -> [ipv4-bar0-1 (l:0) 0:--/--], done=False, patterns=1]   Nxt-State: 1
  Match: ([ff, f0, 00, 00, 00], [03, 60, 00, 00, 00])   Next-State:   2/255   Adv:   0   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  7,  0), ( 0,  8, 37), ( 0,  0,  0)]     # Match: [[mpls-pseudo-1 (l:0) 0:--/0] -> [ipv6-1 (l:40) 0:--/--], done=False, patterns=1]   Nxt-State: 2
  Match: ([ff, 01, 00, 01, 00], [04, 00, 00, 00, 00])   Next-State:   4/255   Adv:   8   Next-Lookup: [0, 4]   Hdr-Starts: [( 2,  3,  4), ( 6,  4,  4), ( 0,  0,  0)]     # Match: [[mpls-1 (l:4) 2:3/3] -> [mpls-2 (l:4) 0:3/3] -> [mpls-3 (l:4) 0:1/1], done=False, patterns=1]   Nxt-State: 4
  Match: ([ff, 01, 00, 01, 00], [04, 00, 00, 01, 00])   Next-State:   3/255   Adv:   6   Next-Lookup: [0, 0]   Hdr-Starts: [( 2,  3,  4), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[mpls-1 (l:4) 2:3/3] -> [mpls-2 (l:4) 0:3/3] -> [mpls-pseudo-bar0-1 (l:0) 0:--/--], done=False, patterns=1]   Nxt-State: 3
  Match: ([ff, 01, 00, 00, 00], [04, 01, 00, 00, 00])   Next-State:   3/255   Adv:   2   Next-Lookup: [0, 0]   Hdr-Starts: [( 0,  0,  0), ( 0,  0,  0), ( 0,  0,  0)]     # Match: [[mpls-1 (l:4) 2:3/3] -> [mpls-pseudo-bar0-1 (l:0) 0:--/--], done=False, patterns=1]   Nxt-State: 3
"""

def hex_dig_to_bits(dig: str) -> list[bool]:
  binary_byte = bin(int(dig, base=16))
  # Use zfill to pad the string with zeroes as we want all 8 digits of the byte.
  bits_string = binary_byte[2:].zfill(4)
  return [bool(int(bit)) for bit in bits_string]

# 0001 -> 3
def bits_to_slice_lo(bits: list[bool]) -> int:
  pref_idx = 0
  try:
    pref_idx = bits.index(True) 
    suf = bits[pref_idx:]

    for b in suf:
      assert b
    
  except ValueError:
    pass
  finally:
    return len(bits) - pref_idx

def hex_digs_to_slices(digs: str) -> tuple[int, int]:
  base = 0
  ret = []
  for dig in digs:
    print("converting", dig)
    lo = bits_to_slice_lo(hex_dig_to_bits(dig)) + base
    ret.append((base+4, lo))

    base += 4
  return ret
