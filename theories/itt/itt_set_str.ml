doc <:doc<
   @begin[doc]
   @module[Itt_set_str]

  In this module we define the most common data structures: Sets and Tables.

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1998 Jason Hickey, Cornell University

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Alexei Kopylov
   @email{kopylov@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   This module depends on the following ones:
   @end[doc]
>>
extends Itt_record
extends Itt_algebra_df
extends Itt_logic
extends Itt_union2
doc <:doc< @docoff >>

open Dtactic

doc <:doc<
   @begin[doc]
   @modsection{Set data structure}
   Set is a data structures for storing collection of values.
   @modsubsection{Definitions}

   Here is a definition of a data structure Set.
   @end[doc]
>>

define set_sig: Set[i:l]{'T} <-->
   {car : univ[i:l];
    empty : ^car;
    member : ^car -> 'T -> bool;
    insert : ^car -> 'T -> ^car;
    delete : ^car -> 'T -> ^car;
    all a:'T. not{"assert"{^member (^empty) 'a}} ;
    all S:^car. all a:'T. all b:'T. iff{"assert"{^member (^insert 'S 'b) 'a}; ."assert"{^member 'S 'a} or 'a='b in 'T};
    all S:^car. all a:'T. all b:'T. iff{"assert"{^member (^delete 'S 'b) 'a}; ."assert"{^member 'S 'a} and not{'a='b in 'T}}
   }

doc <:doc< @docoff >>

dform set_df : except_mode[src] :: Set[i:l]{'T} = mathbbS `"et" sub{slot[i:l]} "(" 'T ")"

interactive set_intro  {| intro[] |}:
[wf]sequent { <H> >- "type"{'T} } -->
   sequent { <H> >- 'set in {car: univ[i:l]} } -->
   sequent { <H> >- 'set in {empty : 'set^car} }-->
   sequent { <H> >- 'set in {member : 'set^car -> 'T -> bool} } -->
   sequent { <H> >- 'set in {insert : 'set^car -> 'T -> 'set^car} }-->
   sequent { <H> >- 'set in {delete : 'set^car -> 'T -> 'set^car} } -->
   sequent { <H> >- all a:'T. not{"assert"{('set^member) ('set^empty) 'a}} } -->
   sequent { <H> >- all S:'set^car. all a:'T. all b:'T. iff{"assert"{('set^member) (('set^insert) 'S 'b) 'a}; ."assert"{(('set^member) 'S 'a)} or 'a='b in 'T} } -->
   sequent { <H> >- all S:'set^car. all a:'T. all b:'T. iff{"assert"{('set^member) (('set^delete) 'S 'b) 'a}; ."assert"{(('set^member) 'S 'a)} and not{'a='b in 'T}} } -->
   sequent { <H> >- 'set in Set[i:l]{'T} }

 doc <:doc<
   @begin[doc]
   The <<label["car":t]>> is an abstract carrier for sets (in concrete implementations it could be, for example, list or tree type),
   <<label["empty":t]>> is a constant of this type for an empty set.
   Set data type has also the following functions:
   @begin[itemize]
    @item{ <<label["member":t] 'S 'a>> checks whether element $a$ is a member of set $S$.}
    @item{ <<label["insert":t] 'S 'a>> inserts element $a$ in set $S$.}
    @item{<<label["delete":t] 'S 'a>> deletes element $a$ from set $S$.}
   @end[itemize]

   There are three specifications that guarantees that sets works properly:
  @begin[itemize]
    @item{ << not{"assert"{(self{'self}^member) (self{'self}^empty) 'a}}>> guarantees that <<label["empty":t]>> is an empty set.}
    @item{ << iff{"assert"{(self{'self}^member) ((self{'self}^insert) 'S 'b) 'a}; ("assert"{((self{'self}^member) 'S 'a)} or 'a='b in 'T)}>>

     guarantees that  <<label["insert":t] 'S 'b>> has all elements that $S$ had, an element $b$ and nothing more.}
    @item{ << iff{"assert"{(self{'self}^member) ((self{'self}^delete) 'S 'b) 'a}; ("assert"{((self{'self}^member) 'S 'a)} and not{'a='b in 'T})}>>

     guarantees that  <<label["delete":t] 'S 'b>> has all elements that $S$ had except element $b$.}
   @end[itemize]
   @end[doc]
>>

doc <:doc<
   @begin[doc]
   @modsubsection{Example: Sets as lists}

   The simplest example of an implementation of Set data structure uses lists.
   The theory @hrefmodule[Itt_fset] already defined
   a type of finite sets as a type of lists,
   quotiented over all permutations:
   $$<< fset{'eq; 'T} >> = << (quot x, y : list{'T} // "assert"{fequal{'eq; 'x; 'y}}) >>$$

  where $T$ is an arbitrary type and <<'eq>> is an equivalence relation on this type.
  Theory @hrefmodule[Itt_fset] also defines some basic operations on this type.
   Here we combine these operations in one data structure.

   Since @hrefmodule[Itt_fset]'s definition of sets needs a  decidable equality,
   we will define a functor that take a type with decidable equality $A$
   and construct a data structure of the type <<Set[i:l]{'A^car}>>.
   @end[doc]
>>
extends Itt_fset
extends Itt_relation_str

doc <:doc<
   @doc{Definition:}
>>
define set_as_list: set_as_list{'A} <-->
   {car =  fset{'A^"=";'A^car};
    empty =  fempty;
    member = lambda {S. lambda{x.fmember{'A^"="; 'x; 'S} }};
    insert = lambda {S. lambda{x.funion{'A^"="; 'S;  fsingleton{'x}} }};
    delete = lambda {S. lambda{x.fsub{'A^"="; 'S;  fsingleton{'x}} }}
   }

doc <:doc< @docoff >>

dform sal_df : except_mode[src] :: set_as_list{'A} = `"set_as_list" "(" 'A ")"

doc <:doc<
   @doc{Theorem:}
>>
interactive set_as_list_correct :
   sequent { <H> >- 'A in  DecEquality[i:l] } -->
   sequent { <H> >- set_as_list{'A} in Set[i:l]{'A^car} }

doc <:doc<
   @begin[doc]
   @modsubsection{Remarks}
    Note that decidable equality is important to define @tt[set_as_list].
    Actually we can prove that it is necessary for a type $T$ to have a decidable equality
    to implement a Set data structure:
   @end[doc]
>>

interactive necessity_of_deicidability univ[i:l]:
   [wf] sequent { <H> >- "type"{'T} } -->
   sequent { <H> >- Set[i:l]{'T} } -->
   sequent { <H> >- all a:'T. all b:'T. decidable{'a='b in 'T} }

doc <:doc<
   @begin[doc]
More efficient implementation of Sets could be defined when type have an order.
We will define such structures in  @hrefmodule[Itt_sorted_tree] and  @hrefmodule[Itt_rbtree].
   @end[doc]
>>

doc <:doc<
   @begin[doc]
   @modsection{Map data structure}

   Another common data structure is Table. A table is a partial function with a finite domain.
   It can be viewed as a set of pairs <<('argument,'value)>>, where the first components of all pairs are different.

   @modsubsection{Definitions}
   @end[doc]
>>

define dep_table_sig: Table[i:l]{'T; x.'M['x]} <-->
   {car : univ[i:l];
    empty : ^car;
    apply : ^car -> x:'T -> 'M['x] + unit;
    insert : ^car -> x:'T -> y:'M['x] -> ^car;
    delete : ^car -> 'T -> ^car;
    all x:'T. ^apply (^empty) 'x = inr{it} in 'M['x] + unit;
    all F:^car. all x:'T. all y:'M['x].
       ^apply (^insert 'F 'x 'y) 'x = inl{'y} in  'M['x] + unit;
    all F:^car. all x_1:'T. all y:'M['x_1]. all x_2:'T.
       (not{'x_1='x_2 in 'T} => ^apply (^insert 'F 'x_2 'y) 'x_1 = ^apply 'F 'x_1 in  'M['x_1] + unit);
    all F:^car. all x:'T.
       ^apply (^delete 'F 'x) 'x = inr{it} in  'M['x] + unit;
    all F:^car. all x_1:'T. all x_2:'T.
       (not{'x_1='x_2 in 'T} => ^apply (^delete 'F 'x_2) 'x_1 = ^apply 'F 'x_1 in  'M['x_1] + unit)
   }

doc <:doc< @docoff >>

dform table_df : except_mode[src] :: Table[i:l]{'T; x.'M} = mathbbT `"able" sub{slot[i:l]} "(" (x:'T -> 'M)  ")"

define table_sig: Table[i:l]{'T;'M} <--> Table[i:l]{'T; x.'M}

dform table_df2 : except_mode[src] :: Table[i:l]{'T; 'M} = mathbbT `"able" sub{slot[i:l]} "(" ('T -> 'M)  ")"

 doc <:doc<
   @begin[doc]
   This definitions says that table data structure has a constant <<label["empty":t]>>
   (an empty table, i.e. function that undefined on all elements).
   Table has also the following functions:
   @begin[itemize]
    @item{ <<label["apply":t] 'F 'a>> applies the function $F$ to $a$.
     It returns <<inr{'y}>>  if $y$ is an result of the application
     and  <<inl{it}>> if $a$ is not in domain of function $F$.
     In other words: it looks for a pair of the form <<'a,'y>> in the table. }
     and returns <<inl{'y}>>  if it finds one and  <<inr{it}>> otherwise.

    @item{ <<label["insert":t] 'F 'a 'b>> defines the value of the function at the point $a$ to be $b$.
   In other words: inserts a pair <<'a,'b>> in table $F$.}

    @item{<<label["delete":t] 'F 'a>> makes the function undefined at the point $a$.
    In other words it deletes a pair <<'a,'y>>
    from table $F$.}
   @end[itemize]

   There are five specifications that guarantees that sets works properly:
  @begin[itemize]
    @item{
   <<label[apply:t] label[empty:t] 'x = inr{it} in 'M['x] + unit >>
    }
    @item{
   <<label[apply:t] (label[insert:t] 'F 'x 'y) 'x = inl{'y} in  'M['x] + unit >>
   }
    @item{
   $<<(not{'x_1='x_2 in 'T} => label[apply:t] (label[insert:t] 'F 'x_2 'y) 'x_1 = label[apply:t] 'F 'x_1 in  'M['x_1] + unit) >>$
    }
    @item{
   << label[apply:t] (label[delete:t] 'F 'x) 'x = inl{it} in  'M['x] + unit >>
    }
    @item{
   $<< (not{'x_1='x_2 in 'T} => label[apply:t] (label[delete:t] 'F 'x_2) 'x_1 = label[apply:t] 'F 'x_1 in  'M['x_1] + unit) >>$
    }
   @end[itemize]
   @end[doc]
>>

 doc <:doc<
   @begin[doc]
   @modsubsection{Sets as tables}
   Set is partial case of Table. We can construct a data structure $Set:<<Set[i:l]{'T}>>$ of sets of elements of type $T$
   from a given table $Table:<<Table[i:l]{'T; unit}>>$.
   @end[doc]
>>

define set_as_table: set_as_table{'Table} <-->
   {car =  'Table^car;
    empty =  'Table^empty;
    member = lambda {S. lambda{x. is_inl{'Table^apply 'S 'x} }};
    insert = lambda {S. lambda{x. 'Table^insert 'S 'x it}};
    delete = 'Table^delete
   }

interactive set_as_table_correct :
   sequent { <H> >- "type"{'T} } -->
   sequent { <H> >- 'Table in Table[i:l]{'T;unit} } -->
   sequent { <H> >- set_as_table{'Table} in Set[i:l]{'T} }

(*
doc <:doc<
   @begin[doc]
   @modsubsection{Tables as lists}

   The simplest way to implement Tables is to use lists as carrier in the same way as we defined sets.

   Let us construct a <<Table[i:l]{'A^car; x.'S['x]}>>, where $A$ is an ordered set.
   @end[doc]
>>

doc <:doc< @docoff >>
define rel_prod: rel_prod{'R_1;'R_2} <--> lambda {a. lambda {b. 'R_1 fst{'a} fst{'b} band  'R_2 snd{'a} snd{'b} }}
define rel_true: rel_true <--> lambda {a. lambda {b. btrue }}
doc <:doc< @doc >>

define set_as_list: set_as_list{'A} <-->
   {car =  fset{rel_prod{'A^"="; rel_true};. 'A^car * 'S['x]};
    empty =  fempty;
    apply =
    insert = lambda {S. lambda{x.lambda{y.funion{'A^"="; 'S;  fsingleton{'x,'y}} }};
    delete = lambda {S. lambda{x.lambda{y.fsub{'A^"="; 'S;  fsingleton{'x,'y}} }}
   }

doc <:doc< @docoff >>

dform sal_df : except_mode[src] :: set_as_list{'A} = `"set_as_list" "(" 'A ")"

doc <:doc<
   @doc{Theorem:}
>>
interactive set_as_list_correct :
   sequent { <H> >- 'A in  DecEquality[i:l] } -->
   sequent { <H> >- set_as_list{'A} in Set[i:l]{'A^car} }

*)

doc <:doc< @docoff >>
