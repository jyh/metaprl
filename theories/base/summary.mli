(*
 * These are the declares for the terms in a Filter_summary.summary_item.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Perv
include Nuprl_font
include Base_dform
include Ocaml_df

declare "interface"{'intf}
declare "implementation"{'impl}
declare "location"[start:n, finish:n]{'body}

declare "rewrite"[name:s]{'redex; 'contractum; 'proof}
declare "cond_rewrite"[name:s]{'params; 'args; 'redex; 'contractum; 'proof}
declare "axiom"[name:s]{'stmt; 'proof}
declare "rule"[name:s]{'params; 'stmt; 'proof}
declare "opname"[name:s]{'term}
declare "mlterm"{'term; 'cons; 'oexpr}
declare "condition"{'term; 'cons; 'oexpr}
declare "parent"{'path; 'opens; 'resources}
declare "module"[name:s]{'info}
declare "dform"{'modes; 'redex; 'def}
declare "prec"[name:s]
declare "prec_rel"{'op; 'left; 'right}
declare "id"{'id}
declare "resource"[name:s]{'extract; 'improve; 'data}
declare "infix"[name:s]
declare "magic_block"[name:s]{'items}
declare "summary_item"{'term}

declare "inherit_df"
declare "prec_df"[name:s]
declare "parens_df"
declare "mode_df"[mode:s]

declare "df_none"
declare "df_term"{'t}
declare "df_ml"[printer:s, buffer:s]{'contracta; 'code}

declare "none"
declare "some"{'t}

declare "meta_theory"{'A}
declare "meta_theorem"{'A}
declare "meta_implies"{'A; 'B}
declare "meta_function"{'A; x. 'B['x]}
declare "meta_iff"{'A; 'B}

declare "context_param"[name:s]
declare "var_param"[name:s]
declare "term_param"{'t}

(* Proofs *)
declare "interactive"{'t}

declare "status_bad"
declare "status_partial"
declare "status_asserted"
declare "status_complete"

declare "proof_step"{'goal; 'subgoals; 'ast; 'text}
declare "proof_node"{'proof}

declare "proof_child_goal"{'goal}
declare "proof_child_proof"{'proof}

declare "proof_aterm"{'goal; 'label; 'args}

declare "proof_var_args"{'args}
declare "proof_term_args"{'args}
declare "proof_type_arg"{'arg}
declare "proof_int_args"{'args}
declare "proof_thin"
declare "proof_dont_thin"
declare "proof_subst_arg"{'args}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
