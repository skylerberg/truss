type t = {
  core : Resolve.Names.key -> Core.t;
  spans : Resolve.Names.key -> Source.Definition_span.t array;
  text : Resolve.Names.key -> string;
  interface : Interface.Lookups.t;
}
