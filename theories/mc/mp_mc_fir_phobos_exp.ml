(*!
 * @begin[doc]
 * @theory[Mp_mc_fir_phobos_exp]
 *
 * The @tt[Mp_mc_fir_phobos_exp] module provides term declarations
 * for the Phobos FIR output.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Base_theory
(*! @docoff *)

declare variable[v:s]
declare string[s:s]
declare number[n:s]

declare letUnop[v:s]{ 'ty; 'unop; 'a}
declare letBinop[v:s]{ 'ty; 'binop; 'a1; 'a2 }
declare letExt[v:s]{'ty1; 'filename; 'ty2; 'args}
declare call{'label; 'f; 'args}
declare letAlloc[v:s]{'op}
declare letSubscript[v:s]{'op; 'ty; 'v2; 'a}
declare setSubscript{'op; 'label; 'var; 'a1; 'ty; 'a2}
declare setGlobal{'sub_value; 'label; 'var; 'ty; 'a}
declare memcpy{'op; 'label; 'v1; 'a1; 'v2; 'a2; 'a3}
declare assertExp{'var; 'pred}
declare debug{'debug_info}
declare tailCall_com[f:s]{'label; 'f; 'params}
declare specialCall{'label; 'tailop}
declare matchExp{'a; 'list}
declare typeCase{'a1; 'a2; 'v1; 'v2; 'e1; 'e2}

