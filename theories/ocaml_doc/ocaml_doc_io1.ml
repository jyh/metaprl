doc <:doc< -*- Mode: text -*-

   @begin[spelling]
   bprintf dd ddd dddd deallocates eprintf excl fprintf gen int ll nonblock
   printf rdonly sprintf stderr stdout trunc wronly creat
   @end[spelling]

   @begin[doc]
   @chapter[io]{Input and Output}
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2000 Jason Hickey, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @docoff >>
extends Base_theory

doc <:doc<
@begin[doc]

The I/O library in OCaml is fairly expressive, including a @tt{Unix}
library that implements most of the portable Unix system calls.  In
this chapter, we'll cover many of the standard built-in I/O functions.

The I/O library uses two data types: the @code{in_channel} is the
type of I/O channels from which characters can be read, and the
@code{out_channel} is an I/O channel to which characters can be
written.  I/O channels may represent files, communication
channels, or some other device; the exact operation depends on the
context.

At program startup, there are three channels open, corresponding to
the standard file descriptors in Unix.

@begin[verbatim]
val stdin : in_channel
val stdout : out_channel
val stderr : out_channel
@end[verbatim]

@section[file_opening]{File opening and closing}

There are two functions to open an output file: the @code{open_out}
function opens a file for writing text data, and the
@code{open_out_bin} opens a file for writing binary data.  These two
functions are identical on a Unix system.  On a Macintosh or Windows
system, the @code{open_out} function performs line termination
translation (why do all these systems use different line
terminators?), while the @code{open_out_bin} function writes the data
exactly as written.  These functions raise the @code{Sys_error}
exception if the file can't be opened; otherwise they return an
@code{out_channel}.

A file can be opened for reading with the functions @code{open_in}
and @code{open_in_bin}.

@begin[verbatim]
val open_out : string -> out_channel
val open_out_bin : string -> out_channel
val open_in : string -> in_channel
val open_in_bin : string -> in_channel
@end[verbatim]

The @code{open_out_gen} and @code{open_in_gen} functions can be used
to perform more sophisticated file opening.  The function requires an
argument of type @code{open_flag} that describes exactly how to open
the file.

@begin[verbatim]
type open_flag =
    Open_rdonly | Open_wronly | Open_append
  | Open_creat | Open_trunc | Open_excl
  | Open_binary | Open_text | Open_nonblock
@end[verbatim]

These opening modes have the following interpretation.

@begin[description]
@item{Open_rdonly; open for reading}
@item{Open_wronly; open for writing}
@item{Open_append; open for appending}
@item{Open_creat; create the file if it does not exist}
@item{Open_trunc; empty the file if it already exists}
@item{Open_excl; fail if the file already exists}
@item{Open_binary; open in binary mode (no conversion)}
@item{Open_text; open in text mode (may perform conversions)}
@item{Open_nonblock; open in non-blocking mode}
@end[description]

The @tt{open_in_gen} and @tt{open_out_gen} functions have
types
@begin[verbatim]
val open_in_gen : open_flag list -> int -> string -> in_channel.
val open_out_gen : open_flag list -> int -> string -> out_channel.
@end[verbatim]
The @code{open_flag list} describe how to open the file, the @tt{int}
argument describes the Unix mode to apply to the file if the file is
created, and the @code{string} argument is the name of the file.

The closing operations @code{close_out} and @code{close_in} close the
channels.  If you forget to close a file, the garbage
collector will eventually close it for you.  However, it is good
practice to close the channel manually when you are done with it.

@begin[verbatim]
val close_out : out_channel -> unit
val close_in : in_channel -> unit
@end[verbatim]

@section[io_values]{Writing and reading values on a channel}

There are several functions for writing values to an
@code{out_channel}.  The @code{output_char} writes a single character
to the channel, and the @code{output_string} writes all the characters
in a string to the channel.  The @code{output} function can be used to
write part of a string to the channel; the @tt{int} arguments are the
offset into the string, and the length of the substring.

@begin[verbatim]
val output_char : out_channel -> char -> unit
val output_string : out_channel -> string -> unit
val output : out_channel -> string -> int -> int -> unit
@end[verbatim]

The input functions are slightly different.  The @code{input_char}
function reads a single character, and the @code{input_line} function
reads an entire line, discarding the line terminator.  The @tt{input}
functions raise the exception @code{End_of_file} if the end of the
file is reached before the entire value could be read.

@begin[verbatim]
val input_char : in_channel -> char
val input_line : in_channel -> string
val input : in_channel -> string -> int -> int -> int
@end[verbatim]

There are also several functions for passing arbitrary OCaml values
on a channel opened in binary mode.  The format of these values is
implementation specific, but it is portable across all standard
implementations of OCaml.  The @code{output_byte} and
@code{input_byte} functions write/read a single byte value.  The
@code{output_binary_int} and @tt{input_binary_int} functions
write/read a single integer value.

The @code{output_value} and @code{input_value} functions write/read
arbitrary OCaml values.  These functions are unsafe!  Note that the
@code{input_value} function returns a value of arbitrary type
@code{'a}.  OCaml makes no effort to check the type of the value read
with @code{input_value} against the type of the value that was written
with @code{output_value}.  If these differ, the compiler will not
know, and most likely your program will generate a segmentation fault.

@begin[verbatim]
val output_byte : out_channel -> int -> unit
val output_binary_int : out_channel -> int -> unit
val output_value : out_channel -> 'a -> unit
val input_byte : in_channel -> int
val input_binary_int : in_channel -> int
val input_value : in_channel -> 'a
@end[verbatim]

@section[channel_manip]{Channel manipulation}

If the channel is a normal file, there are several functions that can
modify the position in the file.  The @code{seek_out} and
@code{seek_in} function change the file position.  The @code{pos_out}
and @code{pos_in} function return the current position in the file.
The @code{out_channel_length} and @code{in_channel_length} return the
total number of characters in the file.

@begin[verbatim]
val seek_out : out_channel -> int -> unit
val pos_out : out_channel -> int
val out_channel_length : out_channel -> int
val seek_in : in_channel -> int -> unit
val pos_in : in_channel -> int
val in_channel_length : in_channel -> int
@end[verbatim]

If a file may contain both text and binary values, or if the mode of the
the file is not know when it is opened, the @code{set_binary_mode_out}
and @code{set_binary_mode_in} functions can be used to change the file
mode.

@begin[verbatim]
val set_binary_mode_out : out_channel -> bool -> unit
val set_binary_mode_in : in_channel -> bool -> unit
@end[verbatim]

The channels perform @emph{buffered} I/O.  By default, the characters on an
@code{out_channel} are not all written until the file is closed.  To
force the writing on the buffer, use the @code{flush} function.

@begin[verbatim]
val flush : out_channel -> unit
@end[verbatim]

@section[printf]{Printf}

The regular functions for I/O can be somewhat awkward.  OCaml also
implements a @tt{printf} function similar to the @tt{printf} in
Unix/C.  These functions are defined in the library module
@code{Printf}.  The general form is given by @code{fprintf}.

@begin[verbatim]
val fprintf: out_channel -> ('a, out_channel, unit) format -> 'a
@end[verbatim]

Don't be worried if you don't understand this type definition.  The
@code{format} type is a built-in type intended to match a format
string.  The normal usage uses a format string.  For example, the
following statement will print a line containing an integer $i$ and a
string $s$.

@begin[verbatim]
fprintf stdout "Number = %d, String = %s\n" i s
@end[verbatim]

The strange typing of this function is because OCaml checks the type
of the format string and the arguments.  For example, OCaml analyzes
the format string to tell that the following @code{fprintf} function
should take a @tt{float}, @tt{int}, and @tt{string} argument.

@begin[verbatim]
# let f = fprintf stdout "Float = %g, Int = %d, String = %s\n";;
Float = val f : float -> int -> string -> unit = <fun>
@end[verbatim]

The format specification corresponds roughly to the C specification.
Each format argument takes a width and length specifier that
corresponds to the C specification.

@begin[description]
@item{d or i; convert an integer argument to signed decimal}
@item{u; convert an integer argument to unsigned decimal}
@item{x; convert an integer argument to unsigned hexadecimal, using
   lowercase letters.}
@item{X; convert an integer argument to unsigned hexadecimal, using
   uppercase letters}
@item{s; insert a string argument}
@item{c; insert a character argument}
@item{f; convert a floating-point argument to decimal notation, in the
   style @emph{dddd.ddd}}
@item{e or E; convert a floating-point argument to decimal notation,
   in the style @emph{d.ddd e+-dd} (mantissa and exponent)}
@item{g or G; convert a floating-point argument to decimal notation,
   in style @emph{f} or @emph{e}, @emph{E} (whichever is more compact)}
@item{b; convert a Boolean argument to the string @tt{true} or
   @tt{false}}
@item{a; {user-defined printer.  It takes two arguments; it applies the
     first one to the current output channel and to the second
     argument. The first argument must therefore have type
     @code{out_channel -> 'b -> unit} and the second one has type
     @code{'b}. The output produced by the function is therefore
     inserted into the output of @tt{fprintf} at the current point.}}
@item{t; same as %a, but takes only one argument (with type
     @code{out_channel -> unit}) and applies it to the current
     @code{out_channel}.}
@item{%; takes no argument and output one @tt{%} character.}
@end[description]

The @tt{Printf} module also provides several additional functions for
printing on the standard channels.  The @tt{printf} function prints in
the channel @tt{stdout}, and @tt{eprintf} prints on @tt{stderr}.

@begin[verbatim]
let printf = fprintf stdout
let eprintf = fprintf stderr
@end[verbatim]

The @tt{sprintf} function has the same format specification as
@tt{printf}, but it prints the output to a string and returns the
result.

@begin[verbatim]
val sprintf: ('a, unit, string) format -> 'a
@end[verbatim]

@section[buffer]{String buffers}

The @tt{Buffer} library module provides string buffers.  The string
buffers can be significantly more efficient that using the native
string operations.  String buffers have type @code{Buffer.t}.  The
type is @emph{abstract}, meaning that the implementation of the buffer
is not specified.  Buffers can be created with the
@code{Buffer.create} function.

@begin[verbatim]
type t (* Abstract type of string buffers *)
val create : unit -> t
@end[verbatim]

There are several functions to examine the state of the buffer.  The
@tt{contents} function returns the current contents of the buffer as a
string.  The @tt{length} function returns the total number of
characters stored in the buffer.  The @tt{clear} and @tt{reset}
function remove the buffer contents; the difference is that @tt{reset}
also deallocates the internal storage used to save the current
contents.

@begin[verbatim]
val contents : t -> string
val length : t -> int
val clear : t -> unit
val reset : t -> unit
@end[verbatim]

There are also several functions to add values to the buffer.  The
@code{add_char} function appends a character to the buffer contents.
The @code{add_string} function appends a string to the contents; there
is also an @code{add_substring} function to append part of a string.
The @code{add_buffer} function appends the contents of another buffer,
and the @code{add_channel} reads input off a channel and appends it to
the buffer.

@begin[verbatim]
val add_char : t -> char -> unit
val add_string : t -> string -> unit
val add_substring : t -> string -> int -> int -> unit
val add_buffer : t -> t -> unit
val add_channel : t -> in_channel -> int -> unit
@end[verbatim]

The @code{output_buffer} function can be used to write the contents of
the buffer to an @code{out_channel}.

@begin[verbatim]
val output_buffer : out_channel -> t -> unit
@end[verbatim]

The @tt{Printf} module also provides formatted output to a string
buffer.  The @tt{bprintf} function takes a @tt{printf}-style format
string, and formats output to a buffer.

@begin[verbatim]
val bprintf: Buffer.t -> ('a, Buffer.t, unit) format -> 'a
@end[verbatim]

@end[doc]
@docoff
>>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
