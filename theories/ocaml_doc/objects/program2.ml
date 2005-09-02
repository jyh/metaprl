(*
 * Object programs.
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

(*
 * Wrapper around the Graphics module.
 *)
module Window =
struct
   type point = int * int
   type color = Graphics.color

   let () =
      Graphics.open_graph ""

   let set_color = Graphics.set_color
   let moveto (x, y) = Graphics.moveto x y
   let lineto (x, y) = Graphics.lineto x y
   let draw_rect (x1, y1) (x2, y2) =
      let x, dx =
         if x1 < x2 then
            x1, x2 - x1
         else
            x2, x1 - x2
      in
      let y, dy =
         if y1 < y2 then
            y1, y2 - y1
         else
            y2, y1 - y2
      in
         Graphics.draw_rect x y dx dy
   let fill_rect (x1, y1) (x2, y2) =
      let x, dx =
         if x1 < x2 then
            x1, x2 - x1
         else
            x2, x1 - x2
      in
      let y, dy =
         if y1 < y2 then
            y1, y2 - y1
         else
            y2, y1 - y2
      in
         Graphics.fill_rect x y dx dy
end;;

(*
 * A generic kind of geometric object.
 *)
class virtual drawable =
object
   method virtual draw : unit
end;;

(*
 * Objects with positions and colors.
 *)
class virtual drawable_item color_init =
object
   inherit drawable
   val mutable color : Window.color = color_init
   method set_color c = color <- c
end;;

(*
 * A generic object with a color and 2 points.
 *)
class virtual two_point_item color_init p1_init p2_init =
object
   inherit drawable_item color_init
   val mutable p1 = p1_init
   val mutable p2 = p2_init
end;;

(*
 * A line.
 *)
class line color_init p1_init p2_init =
object
   inherit two_point_item color_init p1_init p2_init
   method draw =
      Window.set_color color;
      Window.moveto p1;
      Window.lineto p2
end;;

(*
 * A rectangle.
 *)
class rect color_init p1_init p2_init =
object
   inherit two_point_item color_init p1_init p2_init
   method draw =
      Window.set_color color;
      Window.fill_rect p1 p2
end;;

(*
 * A list of items.
 *)
class type container_type =
object
   method add : drawable -> unit
   method draw : unit
end;;

class container : container_type =
object
   inherit drawable

   val mutable items : drawable list = []

   method add item =
      items <- item :: items

   method draw =
      List.iter (fun item -> item#draw) items
end;;

(*
 * A starburst.
 *)
class blocks color point =
object (self)
    inherit container

    initializer
        let x, y = point in
           for i = 0 to 9 do
              let x_left = x + i * 20 in
                 self#add (new rect color (x_left, y) (x_left + 10, y + 10) :> drawable);
           done
end;;

(*
 * Main program.
 *)
let main () =
   let items = new container in
      items#add (new line Graphics.red (0, 0) (100, 100) :> drawable);
      items#add (new blocks Graphics.blue (100, 100) :> drawable);
      items#draw;
      ignore (Graphics.wait_next_event [Graphics.Button_down])

let _ = main ()

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
