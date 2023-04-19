open Game_loop;;

let main () =
  print_endline "Guess the number!";
  Random.self_init ();
  let secret_number = Random.int 100 in
  game_loop secret_number true;;

main ()
