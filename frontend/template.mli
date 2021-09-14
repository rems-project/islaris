open Extra

(** Type of a template: a string with place-holders identified by keys. *)
type template

(** Short synonym of [template]. *)
type t = template

(** [make keys s] constructs a template from the string description [s], whose
    sub-strings of the form ["{ident}"] are bound to keys (here, ["ident"]). A
    set of valid keys (without braces) is given by [keys]. If [s] identifies a
    key not in [keys] then [Invalid_argument] is raised. *)
val make : SSet.t -> string -> t

(** [used_keys t] gives the set of keys effectively appearing in template [t].
    Note that the returned set is always a subset of the [keys] arguments that
    was provided to [make] for creating [t]. *)
val used_keys : t -> SSet.t

(** [subst t m] generates a string from the template [t], replacing keys using
    the corresponding strings in the map [m]. The domain of [m] should exactly
    correspond to the valid keys for [t] (given by the [keys] argument used to
    build [t] with [make]), otherwise [Invalid_argument] is raised. *)
val subst : t -> string SMap.t -> string
