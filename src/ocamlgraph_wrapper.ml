open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)
