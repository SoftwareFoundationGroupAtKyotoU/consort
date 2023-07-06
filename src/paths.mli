(**
   The Path module represents access paths, i.e., symbolic paths through in-memory structures. These are
   used extensively to give canonical, symbolic names to the contents of references.
*)

(** 
   The suffix of an access path gives further description of the
   value being pointed to by the access path. With the exception of `None,
   all of these suffixes represent non-reference values and cannot be
   extended
 *)
type suff = [`Len (** The length of an array *) | `Ind (** The (pseudo-)index variable of an array. *) | `Elem (** The element of an array *) | `None | `Null (** The null flag of a pointer *) ] [@@deriving sexp]
                                                   
(** The root of an access path, where the path through memory begins *)
type root = private
  | Pre of string (** A variable which roots the path in a hypothetical copy of the heap as it appeared at method entry. Used for summarization *)
  | Var of string (** A plain variable *)
  | Ret (** The value returned from a method *)
  | T (** A template parameter. A path rooted in T is a template, and denotes an extension which may be appended to an existing path with root_at below *) [@@deriving sexp]

(** Steps through the heap. Unlike suffixes, which represent a terminal step, these steps may be arbitrarily composed and concatenated *)
type steps = [
  | `Deref (** Follow a (non-null) memory address *)
  | `Proj of int (** The ith element of a tuple *)
  | `Cons of string * int (** The constructor and index of it of data types. For example, in case of LinkedList = Nil | Cons of int * ref LinkedList, the reference part of Cons is represented as Cons("Cons", 2) *)
] [@@deriving sexp]

(** A path is a tuple consisting of a root, a series of steps through the heap, followed by an (optional) final path. This type is
private (to protect crucial invariants), but may still be pattern matched over. To make extension O(1), the steps are stored in _reverse_ order
in the path representation; i.e., the last step is the head of the list, etc. *)
type path = private root * steps list * suff [@@deriving sexp]
type concr_ap = path [@@deriving sexp]

(** Give a string representation of the path, suitable for use as a z3 identifier *)
val to_z3_ident : path ->  string

(** Synonym for to_z3_ident. Defined for use with ppx_custom_printf *)
val to_string : path -> string

(** {2 Extensions}

These functions extend paths. Only non-terminal paths can be extended; attempts to extend a terminal path will result in an exception.
   A terminal path is one with a non-[`None] suffix; paths with these suffixes cannot point to reference types and thus extending them
   never makes sense *)

(** Extend the path with a projection through tuple index i *)
val t_ind : path -> int -> path
    
(** Terminate path at the [`Elem] suffix  *)
val elem : path -> path
    
(** Extend the path with pointer dereference *)
val deref : path -> path

(** Terminate the path at the [`Len] suffix *)
val len : path -> path
    
(** Terminate the path at the [`Ind] suffix *)
val ind : path -> path
    
(** Translate the path to a reference into a path to the [`Null] pseudo-flag *)
val to_null : path -> path
    
(** Extend the path with an element of [steps] *)
val extend : path -> steps -> path
    
(** Extend the path with constructor and index of data types *)
val t_cons : path -> string -> int -> path

(** {2 Constructors}

These functions are the public facing methods for creating path instances *)

(** A path rooted at variable v *)
val var: string -> path

(** A path rooted at the symbolic name for argument i *)
val arg : int -> path

(** The symbolic name for argument i *)
val arg_name : int -> string
    
(** The special return value root *)
val ret : path
  
(** The template root *)
val template : path 

(** Translate a Var-rooted path to its equivalent Pre version. Template paths and Ret paths cannot be converted, and this function will fail is this is attempted. No effect on Pre-rooted paths *)
val pre : path -> path 

(** {2 Queries}

These functions give information about a path  *)

(** Does path [p] have path [prefix] as prefix *)
val has_prefix : prefix:path -> path -> bool

(** Is this path rooted in pre? *)
val is_pre : path -> bool

(** Does this path have no steps and no suffixes? *)
val is_root : path -> bool


(** Can this path only point to unchanging locations? Paths that traverse any mutable memory, i.e. derefs or array elements, are not considered const.
This operation is not defined on template paths, and return rooted paths are considered non-const *)
val is_const_ap : path -> bool

(** Does a Pre- or Var-rooted path have the given variable name as its root? Always false for template and ret paths *)
val has_root : string -> path -> bool

(** As above, but instead of string equality, check according to the given predicate *)
val has_root_p : (string -> bool) -> path -> bool

(** Is this path a template? *)
val is_template : path -> bool

(** Append the steps (and any suffix) template-rooted path given in child to the non-terminal path given by [parent] *)
val root_at : child:path -> parent:path -> path

(** Give the immediate parent of this path. Undefined on paths with no parent, and will throw an exception *)
val parent : path -> path

(** Map the string root of a Pre- or Var-rooted path. No-op on Ret paths, undefined on a template path *)
val map_root : (string -> string) -> path -> path

(** Does this path have a nullity flag suffix *)
val is_nullity : path -> bool

(** Is this an array path (with suffix [`Len], [`Ind], or [`Elem]) *)
val is_array_path : path -> bool

(** Get the name of the Var- or Pre-rooted path; fails on ret or template paths *)
val unsafe_get_root : path -> string

(** Compare two paths. All paths are totally ordered, but the ordering is relatively arbitrary *)
val compare : path -> path -> int

(** Get the last element of a path, if it exists. Returns an option which unions the [steps] type and non-trivial suffixes.

   On a path with just a root, this function returns [None].

   Otherwise, on a path with a non-[`None] suffix [s], returns [Some s].
   Otherwise, on a path with a [`None] suffix, returns the head element of steps (i.e., the last deref/projection in the path)
*)
val tail : path -> [`Null | `Deref | `Proj of int | `Len | `Elem | `Ind | `Cons of string * int] option

(** A (printable) set of paths *)
module PathSet : Std.PRINTSET with type elt = path

(** Maps from paths to arbitrary types *)
module PathMap : Map.S with type key = path

(** Ordering module for custom data structures *)
module PathOrd : Set.OrderedType with type t = path
