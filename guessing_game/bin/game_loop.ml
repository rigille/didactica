open Comparison;;
let rec game_loop (secret_number : int) (first : bool) : unit =
  if first then
    print_endline "What's your guess?"
  else
    print_endline "Try again. What's your next guess?";
  print_string "> ";
  let user_input = read_line () in
  match int_of_string_opt user_input with
  | Some guess -> 
    (match compare guess secret_number with
    | Less ->
      print_endline "Too small!";
      game_loop secret_number false
    | Greater ->
      print_endline "Too big!";
      game_loop secret_number false
    | Equal ->
      print_endline "You won, congratulations!")
  | None ->
    print_endline "The guess needs to be a reasonably small natural number";
    game_loop secret_number false;;
