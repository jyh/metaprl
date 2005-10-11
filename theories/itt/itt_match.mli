(*
 * This is an initial attempt at defining something more
 * like real pattern matching.
 *
 * For now, it is just very simple union-of-products.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Itt_union
extends Itt_dprod
extends Itt_dfun
extends Itt_grammar

declare typeclass Case
declare typeclass Cases

declare iform parsed_case{'p : TuplePatt; 'e : Term} : Case
declare iform sequent [parsed_cases] { Ignore : Case >- Ignore } : Cases
declare iform parsed_match{'e : Term; 'cases : Cases} : Term

declare itt_match_case{'p : TuplePatt; 'e : Term} : Nonterminal
declare itt_match_cases{'cases : Cases} : Nonterminal

production itt_term{parsed_match{'e; 'cases}} <--
   tok_match; itt_term{'e}; tok_with; itt_match_cases{'cases}; tok_end

production itt_match_case{'p; 'e} <--
   itt_tuple_patt{'p}; tok_arrow; itt_term{'e}

production itt_match_cases{parsed_cases{| parsed_case{'p; 'e} |}} <--
   opt_pipe; itt_match_case{'p; 'e}

production itt_match_cases{parsed_cases{| <H>; parsed_case{'p; 'e} |}} <--
   itt_match_cases{parsed_cases{| <H> |}}; tok_pipe; itt_match_case{'p; 'e}

(*
 * Reformat as a decide+spread.
 *)
iform parsed_match_pair :
    parsed_match{'e; parsed_cases{| parsed_case{'p1; 'e1}; parsed_case{'p2; 'e2} |}}
    <-->
    decide{'e; x. parsed_spread{'p1; 'x; 'e1}; x. parsed_spread{'p2; 'x; 'e2}}

iform parsed_match_triple :
    parsed_match{'e; parsed_cases{| parsed_case{'p1; 'e1}; parsed_case{'p2; 'e2}; parsed_case{'p3; 'e3}; <H> |}}
    <-->
    decide{'e; x. parsed_spread{'p1; 'x; 'e1};
               y. parsed_match{'y; parsed_cases{| parsed_case{'p2; 'e2}; parsed_case{'p3; 'e3}; <H> |}}}

iform parsed_spread_single :
    parsed_spread{parsed_tuple_patt{| x: it |}; 'y; 'e}
    <-->
    lambda{x. 'e} 'y

iform parsed_spread_pair :
    parsed_spread{parsed_tuple_patt{| x: it; y: it |}; 't1; 't2}
    <-->
    spread{'t1; x, y. 't2}

iform parsed_spread_triple :
    parsed_spread{parsed_tuple_patt{| x: it; y: it; z: it; <H> |}; 't1; 't2}
    <-->
    spread{'t1; x, www. parsed_spread{parsed_tuple_patt{| y: it; z: it; <H> |}; 'www; 't2}}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
