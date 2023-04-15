let () =
  print_endline "Guess the number!";
  print_endline "Please input your guess.";
  let user_input = read_line () in
  match int_of_string_opt user_input with
  | Some guess -> print_endline ("Your guess is: " ^ (string_of_int guess))
  | None -> print_endline "Please guess a number"
