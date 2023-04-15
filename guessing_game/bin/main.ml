let () =
  print_endline "Guess the number!";
  print_endline "Please input your guess.";
  let guess = read_line () in
  print_endline ("Your guess is: " ^ guess)
