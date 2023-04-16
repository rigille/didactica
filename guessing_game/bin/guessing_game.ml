open Guessing_game.Game_loop;;

let main () =
  print_endline "Guess the number!";
  Random.self_init ();
  let secret_number = Random.int 100 in
  print_endline ("DEBUG: the number is: " ^ (string_of_int secret_number));
  game_loop secret_number;;

main ()
