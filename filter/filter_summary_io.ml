(*
 * This module defines an interface for saving information about
 * modules.  We record information about each module interface,
 * to be used in the definition of the module and in submodules.
 *)

open Printf

open Debug

open Refiner.Refiner.Term

open File_base_type

open Filter_type
open Filter_summary
open Filter_summary_type

(*
 * Show the file loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Filter_summary_io%t" eflush


(*
 * Make the summary from the file base.
 * This just improves the FileBase so we can have
 * nested modules.
 *)
module MakeSummaryBase
   (Address : AddressSig)
   (FileBase : FileBaseSig with type cooked = Address.t) =
struct
   (************************************************************************
    * TYPES                                                                *
    ************************************************************************)

   (*
    * Save the proof and tag types.
    *)
   type cooked = FileBase.cooked
   type select = FileBase.select

   type info =
      { info_root : FileBase.info;
        info_path : module_path;
        mutable info_info : cooked
      }

   type t = FileBase.t

   (************************************************************************
    * INHERITED OPERATIONS                                                 *
    ************************************************************************)

   (*
    * Create a new base from the path.
    *)
   let create = FileBase.create
   let set_path = FileBase.set_path

   (************************************************************************
    * LOAD/STORE                                                           *
    ************************************************************************)

   (*
    * Find a specific module given a full pathname.
    *)
   let find base name select =
      if !debug_summary then
         eprintf "Filter_summary_io.find: %a%t" print_string_list name eflush;
      match name with
         [] ->
            raise (EmptyModulePath "Filter_summary_io.find")
       | name'::path ->
            let info = FileBase.find base (String.uncapitalize name') select in
            let info' = Address.find_sub_module (FileBase.info base info) path in
               { info_root = info;
                 info_path = name;
                 info_info = info'
               }

   (*
    * Find the matching module info.
    *)
   let find_match base info select =
      let { info_root = root; info_path = path } = info in
      let root' = FileBase.find_match base root select in
      let info = Address.find_sub_module (FileBase.info base root') (List.tl info.info_path) in
         { info_root = root';
           info_path = path;
           info_info = info
         }

   (*
    * Set the new magic number.
    *)
   let set_magic base { info_root = root } magic =
      FileBase.set_magic base root magic

   (*
    * Create an empty info.
    *)
   let create_info base select dir file =
      let data = Address.create () in
         { info_root = FileBase.create_info base data select dir file;
           info_path = [String.capitalize file];
           info_info = data
         }

   (*
    * Save a module specification.
    * This can only be called at a root.
    *)
   let save base info =
      match info with
         { info_info = info; info_path = [_]; info_root = root } ->
            FileBase.set_info base root info;
            FileBase.save base root
       | _ ->
            raise (Invalid_argument "Filter_summary_io.save")

   (************************************************************************
    * MODULE INFO                                                          *
    ************************************************************************)

   (*
    * Projections.
    *)
   let info base { info_info = data } =
      data

   let sub_info base { info_info = info; info_path = path; info_root = root } name =
      let path' = path @ [name] in
      let info' = Address.find_sub_module info path' in
         { info_info = info';
           info_path = path';
           info_root = root
         }

   let set_info base info data =
      info.info_info <- data

   let name base { info_path = path } =
      List_util.last path

   let pathname base { info_path = path } =
      path

   let root base { info_root = root; info_path = path } =
      { info_root = root;
        info_path = [List_util.last path];
        info_info = FileBase.info base root
      }

   let file_name base { info_root = root } =
      FileBase.full_name base root

   let type_of base { info_root = root } =
      FileBase.type_of base root
end

(*
 * $Log$
 * Revision 1.10  1998/06/22 19:45:20  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.9  1998/06/15 22:32:13  jyh
 * Added CZF.
 *
 * Revision 1.8  1998/06/01 13:53:15  jyh
 * Proving twice one is two.
 *
 * Revision 1.7  1998/05/27 15:13:04  jyh
 * Functorized the refiner over the Term module.
 *
 * Revision 1.6  1998/04/24 19:38:35  jyh
 * Updated debugging.
 *
 * Revision 1.5  1998/04/24 02:42:11  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/02/23 14:46:22  jyh
 * First implementation of binary file compilation.
 *
 * Revision 1.3  1998/02/19 17:14:01  jyh
 * Splitting filter_parse.
 *
 * Revision 1.2  1997/08/06 16:17:34  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:50:59  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.1  1996/09/02 19:43:16  jyh
 * Semi working package management.
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
