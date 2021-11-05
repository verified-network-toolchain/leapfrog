from __future__ import annotations

def preamble () :
  return "Derive Signature for header.\n"

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
  output = "Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.\n"
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


  # Global Instance header_finite: forall n, @Finite (header n) _ _.
  # Proof.
  #   intros n; solve_indexed_finiteness n [8; 16; 24; 32; 40; 48].
  # Qed.

  # Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
  #   {| enum := [ 
  #     existT _ _ Len; existT _ _ Typ; existT _ _ Value;  
  #     existT _ _ Scratch8; existT _ _ Scratch16; existT _ _ Scratch24;
  #     existT _ _ Scratch32; existT _ _ Scratch40   
  #     ] |}.
  # Next Obligation.
  #   solve_header_finite.
  # Qed.
  # Next Obligation.
  # dependent destruction X; subst;
  # repeat (
  #   match goal with
  #   | |- ?L \/ ?R => (now left; trivial) || right
  #   end
  # ).
  # Qed.



def format_headers (hdrs: list[str], widths:dict[str, int]):
  output = preamble()

  widths_ = set(widths.values())

  for w in widths_:
    output += format_one_width(hdrs, widths, w)
  
  output += format_header_eqdec(widths)
  output += format_header_finite(hdrs, widths)

  return output