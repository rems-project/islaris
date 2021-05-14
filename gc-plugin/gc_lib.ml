open Gc
open Printf

let stats : unit -> string = fun _ ->
  let st = stat () in
  let l1 = String.length (sprintf "%.0f" st.minor_words) in
  let l2 = String.length (sprintf "%d" st.top_heap_words) in
  String.concat "" [
    sprintf "minor_collections: %d\n" st.minor_collections;
    sprintf "major_collections: %d\n" st.major_collections;
    sprintf "compactions:       %d\n" st.compactions;
    sprintf "\n";
    sprintf "minor_words:       %*.0f\n" l1 st.minor_words;
    sprintf "promoted_words:    %*.0f\n" l1 st.promoted_words;
    sprintf "major_words:       %*.0f\n" l1 st.major_words;
    sprintf "\n";
    sprintf "top_heap_words:    %*d\n" l2 st.top_heap_words;
    sprintf "heap_words:        %*d\n" l2 st.heap_words;
    sprintf "live_words:        %*d\n" l2 st.live_words;
    sprintf "free_words:        %*d\n" l2 st.free_words;
    sprintf "largest_free:      %*d\n" l2 st.largest_free;
    sprintf "fragments:         %*d\n" l2 st.fragments;
    sprintf "\n";
    sprintf "live_blocks:       %d\n" st.live_blocks;
    sprintf "free_blocks:       %d\n" st.free_blocks;
    sprintf "heap_chunks:       %d\n" st.heap_chunks
  ]
