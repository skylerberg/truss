let bug format = Compiler_bug.bug ~stage:"Writing" format
let output_ty = Storage.of_elements (Ground.builtin UInt8)
let bytes_ty = Storage.view_of_elements (Ground.builtin UInt8)
let ground_types = [ output_ty; bytes_ty ]

open Emit_c.Builder

let output_parameter env =
  match Convention.parameter env Mut output_ty with
  | Some parameter -> parameter
  | None -> bug "storage of no size"

let value_parameter ty = Lowered.Pointer { target = Value ty; writable = false }

let signature env parameters : Lowered.signature =
  { parameters = parameters @ [ output_parameter env ]; result = None; returns = true }

let call env builder ~output (writer : Well_known.t) ty (place : Lowered.place) =
  let parameter, argument =
    match Convention.parameter env Read ty with
    | Some (Pointer _ as parameter) -> (parameter, Lowered.Address { place; writable = false })
    | Some parameter -> (parameter, Copy place)
    | None -> bug "%s is written, and has no size" (Ground.to_string ty)
  in
  emit builder
    (Call
       {
         target =
           Direct
             {
               function_ = Instance (Code { path = Well_known.path writer; type_arguments = [] });
               signature = Convention.signature [ output_parameter env; parameter ] Nothing;
             };
         arguments = [ output; argument ];
         result = Discarded;
       })

let call_with_bytes env builder ~output writer ~elements ~length =
  let view = local builder (Value bytes_ty) in
  emit builder (Assign (at view, Storage.view bytes_ty ~elements ~length));
  call env builder ~output writer bytes_ty (at view)
