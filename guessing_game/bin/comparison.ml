type comparison = Less | Equal | Greater

let compare (m : int) (n : int) : comparison =
  match ((m < n), (m > n)) with
  | (true, false) -> Less
  | (false, true) -> Greater
  | (_, _) -> Equal;;
