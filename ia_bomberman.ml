#! /home/aurelien/.opam/default/bin/ocaml

open Printf ;;
Random.self_init () ;;

(* Types joueurs et bombes *)

type joueur = {
  ligne : int ;
  colonne : int ;
  num_joueur : int ;
  vitesse : int ;
  nb_bombes_restantes : int ;
  deflagration : int ;
  nb_dash : int ;
  nb_pieges : int ;
} 

type bombes = {
  ligne : int ;
  colonne : int ;
  taille : int ;
  instant : float ;
}

type grille = {
  nb_ligne : int ;
  nb_colonne : int ;
  labyrinthe : int array array ;
}


(* Directions *)
let direction_nord = 0
let direction_est = 1
let direction_sud = 2
let direction_ouest = 3
let direction_attente = 4

(* Actions *)
let action_neutre = 0
let action_bombe = 1
let action_dash = 2
let action_piege = 3

(* Lecture des données d'entrée *)
let parsing_ligne ligne =
  Array.map (fun s -> int_of_string s) (Array.of_list (String.split_on_char ' ' ligne)) ;;

let parsing_ligne_grille ligne =
  Array.map (fun s -> int_of_string s) (Array.of_list (String.split_on_char ' ' (String.sub ligne 0 ((String.length ligne)-1)))) ;;

let parsing_ligne_bombe ligne =
  Array.of_list (String.split_on_char ' ' (String.sub ligne 0 ((String.length ligne)-1)))

let lire_entrees fichier =
  let entree = open_in fichier in 
  let instant =  float_of_string (input_line entree) in
  let num_joueur = int_of_string (input_line entree) in
  let dimensions = parsing_ligne (input_line entree) in
  let grille = {nb_ligne = dimensions.(0); nb_colonne = dimensions.(1); labyrinthe = Array.init dimensions.(0) (fun _ -> parsing_ligne_grille (input_line entree))} in
  let nb_bombes = int_of_string (input_line entree) in
  let bombes = Array.init nb_bombes (fun _ -> let bombe = parsing_ligne_bombe (input_line entree) in {ligne = int_of_string bombe.(0); colonne = int_of_string bombe.(1); taille = int_of_string bombe.(2); instant = float_of_string bombe.(3)}) in
  let nb_joueurs = int_of_string (input_line entree) in
  let joueurs = Array.init nb_joueurs (fun _ -> let joueur = parsing_ligne (input_line entree) in {ligne = joueur.(0); colonne = joueur.(1); num_joueur = joueur.(2); vitesse = joueur.(3); nb_bombes_restantes = joueur.(4) ; deflagration = joueur.(5) ; nb_dash = joueur.(6); nb_pieges = joueur.(7)}) in
  let nb_powerups = int_of_string (input_line entree) in
  let powerups = Array.init nb_powerups (fun _ -> parsing_ligne (input_line entree)) in
  (instant, num_joueur, grille, bombes, joueurs, powerups) ;;

(* Fonctions auxiliaires *)

let distance x1 y1 x2 y2 =
  abs (x1-x2) + abs (y1-y2) ;;

let distance_joueur (joueur : joueur) x y =
  distance joueur.ligne joueur.colonne x y ;;

let position_dangereuse x y bombes =
  Array.exists (fun bombe -> (y = bombe.colonne && abs (bombe.ligne - x) <= bombe.taille) || (x = bombe.ligne && abs (bombe.colonne - y) <= bombe.taille)) bombes ;;

let position_dangereuse_joueur (joueur : joueur) bombes =
  position_dangereuse joueur.ligne joueur.colonne bombes ;;

let plus_proche_powerup x y powerups =
  Array.fold_left (fun acc powerup -> if (distance x y (fst acc) (snd acc)) <= (distance x y powerup.(0) powerup.(1)) then acc else (powerup.(0), powerup.(1))) (Int.max_int/2, Int.max_int/2) powerups ;;

let est_dans_grille grille x y = 
  0 <= x && x < grille.nb_ligne && 0 <= y && y < grille.nb_colonne ;;

let est_accessible grille x y =
  0 <= x && x < grille.nb_ligne && 0 <= y && y < grille.nb_colonne && grille.labyrinthe.(x).(y) <> 1 && grille.labyrinthe.(x).(y) <> 2 ;;

let voisins_accessibles grille x y =
  let voisins = [(x+1, y); (x-1, y); (x, y+1); (x, y-1)] in
  List.filter (fun (i, j) -> est_accessible grille i j) voisins ;;

let all_positions_accessibles grille x y =
  let visited = Array.make_matrix grille.nb_ligne grille.nb_colonne false in
  let accessibles = ref [] in

  let rec aux i j =
    visited.(i).(j) <- true ;
    List.iter (fun (i_voisin, j_voisin) -> if not visited.(i_voisin).(j_voisin) then begin accessibles := (i_voisin, j_voisin)::(!accessibles) ; aux i_voisin j_voisin end ; ) (voisins_accessibles grille i j) ;
  in

  if est_accessible grille x y then begin
    accessibles := (x, y) :: (!accessibles) ;
    aux x y ;
  end ;

  List.sort compare !accessibles ;;


(* Calcul d'un plus court chemin : A* *)

let a_star grille (joueur : joueur) destination =

  (* Initialisation *)
  let x0, y0 = joueur.ligne, joueur.colonne in
  let x, y = destination in
  let dOrigine = Array.make_matrix grille.nb_ligne grille.nb_colonne Int.max_int in
  let estimationTotale = Array.make_matrix grille.nb_ligne grille.nb_colonne Int.max_int in
  let visite = Array.make_matrix grille.nb_ligne grille.nb_colonne false in
  let predecesseur = Array.make_matrix grille.nb_ligne grille.nb_colonne (-1, -1) in
  dOrigine.(x0).(y0) <- 0 ;
  estimationTotale.(x0).(y0) <- distance_joueur joueur x y ;

  (* Trouver le sommet avec la plus petite distance *)
  let trouver_min () =
    let min_x, min_y = ref (-1), ref (-1) in
    let min_val = ref max_int in
    for i = 0 to grille.nb_ligne - 1 do
      for j = 0 to grille.nb_colonne - 1 do
        if not visite.(i).(j) && estimationTotale.(i).(j) < !min_val then begin
          min_x := i;
          min_y := j;
          min_val := estimationTotale.(i).(j)
        end
      done
    done;
    (!min_x, !min_y)
  in

  (* Parcours *)
  try
    while not visite.(x).(y) do
      let x_sommet, y_sommet = trouver_min() in
      (* Pas de chemin trouvé *)
      if x_sommet = -1 then raise Exit ;
      visite.(x_sommet).(y_sommet) <- true ;
      let voisins = voisins_accessibles grille x_sommet y_sommet in
      List.iter (fun (x_voisin, y_voisin) ->
        if dOrigine.(x_sommet).(y_sommet) + 1 < dOrigine.(x_voisin).(y_voisin) then begin
          dOrigine.(x_voisin).(y_voisin) <- dOrigine.(x_sommet).(y_sommet) + 1 ;
          predecesseur.(x_voisin).(y_voisin) <- (x_sommet, y_sommet) ;
          visite.(x_voisin).(y_voisin) <- false ;
        end ;
        let d = distance x_voisin y_voisin x y in
        estimationTotale.(x_voisin).(y_voisin) <- min estimationTotale.(x_voisin).(y_voisin) (dOrigine.(x_voisin).(y_voisin)+d) ) voisins ;
      done ;

      let chemin = ref [] and sommet = ref destination in
      while !sommet <> (x0, y0) do
        chemin := !sommet :: !chemin ;
        sommet := predecesseur.(fst !sommet).(snd !sommet) ;
      done ;
      List.hd !chemin ;
    with
    | Exit -> (-1, -1) ;;

(* Calcul des postions bombables les plus intéressantes et où on peut esquiver ultérieurement *)

let gain_max_bombe grille (joueur : joueur) positions_accessibles =
  let gain_bombe x y =
    let gain = ref 0. in
    if grille.labyrinthe.(x).(y) <> 3+joueur.num_joueur then gain := !gain +. 1. ;
    for k=1 to joueur.deflagration do
      if est_dans_grille grille (x+k) y && grille.labyrinthe.(x+k).(y) <> 1 && grille.labyrinthe.(x+k).(y) <> 3+joueur.num_joueur then
        if grille.labyrinthe.(x+k).(y) = 2 then gain := !gain +. 0.5 else gain := !gain +. 1. ;
      if est_dans_grille grille (x-k) y && grille.labyrinthe.(x-k).(y) <> 1 && grille.labyrinthe.(x-k).(y) <> 3+joueur.num_joueur then
        if grille.labyrinthe.(x-k).(y) = 2 then gain := !gain +. 0.5 else gain := !gain +. 1. ;
      if est_dans_grille grille x (y+k) && grille.labyrinthe.(x).(y+k) <> 1 && grille.labyrinthe.(x).(y+k) <> 3+joueur.num_joueur then
        if grille.labyrinthe.(x).(y+k) = 2 then gain := !gain +. 0.5 else gain := !gain +. 1. ;
      if est_dans_grille grille x (y-k) && grille.labyrinthe.(x).(y-k) <> 1 && grille.labyrinthe.(x).(y-k) <> 3+joueur.num_joueur then
        if grille.labyrinthe.(x).(y-k) = 2 then gain := !gain +. 0.5 else gain := !gain +. 1. ;
    done ;
    !gain ;
  in

  let comparaison (x1, y1) (x2, y2) = 
    if gain_bombe x1 y1 >= gain_bombe x2 y2 then -1 else 1
  in

  List.sort comparaison positions_accessibles ;;

let esquivable grille (joueur : joueur) positions_safe bombe =
  let position_safe = List.filter (fun (x, y) -> not (position_dangereuse x y [|bombe|])) positions_safe in
  let position_safe_atteignables = List.filter (fun (x, y) -> (distance_joueur joueur x y) + 1 < int_of_float (bombe.instant /. (0.9**(float_of_int joueur.vitesse)))) position_safe in
  position_safe_atteignables <> [] ;;



let position_a_bomber grille (joueur : joueur) positions_accessibles positions_safe =
  let position_a_bomber = gain_max_bombe grille joueur positions_accessibles in
  let position_safe_a_bomber = List.filter (fun (x, y) -> esquivable grille joueur positions_safe {ligne = x ; colonne = y ; taille = joueur.deflagration ; instant = 5.5}) position_a_bomber in
  (*let position_safe_a_bomber_proche = List.sort (fun (x1, y1) (x2, y2) -> if (distance_joueur joueur x1 y1) >= (distance_joueur joueur x2 y2) then 1 else -1) position_safe_a_bomber in*)
  match position_safe_a_bomber with
  | [] -> None
  | h::t -> Some h


(* Stratégie *)



let decision_strategique instant (num_joueur : int) (grille : grille) (bombes : bombes array) (joueurs : joueur array) powerups =

  let joueur = Option.get (Array.find_opt (fun j -> j.num_joueur = num_joueur) joueurs) in
  let positions_accessibles = all_positions_accessibles grille joueur.ligne joueur.colonne in
  let positions_safe = List.filter (fun (x, y) -> not (position_dangereuse x y bombes)) positions_accessibles in
  let powerups_accessibles = Array.of_list (List.filter (fun powerup -> List.mem (powerup.(0), powerup.(1)) positions_accessibles) (Array.to_list powerups)) in

  (* 1. Éviter les dangers immédiats *)
 
  if position_dangereuse_joueur joueur bombes then begin
    if positions_safe = [] then (direction_attente, action_neutre)
    else begin
      let position_safe = List.hd (List.sort (fun (x1, y1) (x2, y2) -> if distance_joueur joueur x1 y1 >= distance_joueur joueur x2 y2 then 1 else -1) positions_safe) in
      let (next_x, next_y) = a_star grille joueur position_safe in
      if next_x = joueur.ligne - 1 then (direction_nord, action_neutre)
      else if next_x = joueur.ligne + 1 then (direction_sud, action_neutre)
      else if next_y = joueur.colonne - 1 then (direction_ouest, action_neutre)
      else if next_y = joueur.colonne + 1 then (direction_est, action_neutre)
      else (direction_attente, action_neutre)
    end
  end

  (* 2. Collecter des power-ups proches *)
  else if Array.length powerups_accessibles > 0 then begin
    let x_pu, y_pu = plus_proche_powerup joueur.ligne joueur.colonne powerups_accessibles  in
    if x_pu <> Int.max_int && y_pu <> Int.max_int then
      let next_x, next_y = a_star grille joueur (x_pu, y_pu) in
      if next_x = joueur.ligne - 1 then (direction_nord, action_neutre)
      else if next_x = joueur.ligne + 1 then (direction_sud, action_neutre)
      else if next_y = joueur.colonne - 1 then (direction_ouest, action_neutre)
      else if next_y = joueur.colonne + 1 then (direction_est, action_neutre)
      else (direction_attente, action_neutre)
    else (direction_attente, action_neutre)
  end
 
 
  (* 3. Identifier un emplacement stratégique pour poser une bombe *)
  else begin
    let pos_bombe = position_a_bomber grille joueur positions_accessibles positions_safe in
    match pos_bombe with
    | None -> (direction_attente, action_neutre)
    | Some (x_bombe, y_bombe) ->
      if x_bombe = joueur.ligne && y_bombe = joueur.colonne && joueur.nb_bombes_restantes > 0 then (direction_attente, action_bombe)
      else
        let next_x, next_y = a_star grille joueur (x_bombe, y_bombe) in
        if position_dangereuse next_x next_y bombes then (direction_attente, action_neutre)
        else if next_x = joueur.ligne - 1 then (direction_nord, action_neutre)
        else if next_x = joueur.ligne + 1 then (direction_sud, action_neutre)
        else if next_y = joueur.colonne - 1 then (direction_ouest, action_neutre)
        else if next_y = joueur.colonne + 1 then (direction_est, action_neutre)
        else (direction_attente, action_neutre) ;
    end;;

(* Programme principal *)

let main = 
  let instant, num_joueur, grille, bombes, joueurs, powerups = lire_entrees "./entrees.txt" in
  (*strategie_test instant num_joueur grille bombes joueurs powerups ;;*)



  let n, k = decision_strategique instant num_joueur grille bombes joueurs powerups in
  printf "%d %d\n" n k ;;
