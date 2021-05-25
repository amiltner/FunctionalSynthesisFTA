open MyStdLib
open Lang

module Constraints = struct
  type t = (Value.t * Value.t) list
end

module Nonpermitted = struct
  type t = (Value.t * Value.t) list
end

module QE = struct
  type t =
    {
      constraints  : Constraints.t  ;
      nonpermitted : Constraints.t ;
    }
end
