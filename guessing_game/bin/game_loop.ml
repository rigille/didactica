open Comparison;;
let rec game_loop (secret_number : int) : unit =
  print_endline "Please input your guess.";
  let user_input = read_line () in
  match int_of_string_opt user_input with
  | Some guess -> 
    (match compare guess secret_number with
    | Less ->
      print_endline "Too small!";
      game_loop secret_number
    | Greater ->
      print_endline "Too big!";
      game_loop secret_number
    | Equal ->
      print_endline "You won, congratulations!")
  | None ->
    print_endline "Please guess a reasonably small number";
    game_loop secret_number;;
