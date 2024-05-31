/* Asteroids_arcade_game
 * Author: Pragathi Sithmini
 * UoW Id: w1810216
 * IIT Id: 20200351
 * Creation date: 12/15/2023
 */
MACHINE
    Asteroids_arcade_game
    
SETS
    SPACESHIP_MOVEMENTS_STATUS = {successful_movement,
                                     reach_the_space_boundary,
                                     reach_the_asteroid,
                                     failed_for_some_other_reasons,
                                     cannot_move_insufficient_power,
                                     space_ship_placed,
                                     spaceShip_locate_starting_point,
                                     game_not_start,
                                     for_warpDrive_requesting_20_power};
   
    GAME_STATUS = { Game_not_start,
                    Won_the_game,
                    You_lost_the_game,
                    Game_not_over
                  }
               
CONSTANTS
    STARBASE_LOCATION,
    ASTEROITDS_LOCATIONS,
    STARTING_LOCATION,
    X_AXIS_RANGE,
    Y_AXIS_RANGE,
    SPACE_GRID,
    TRIED_TO_MOVE_SPACESHIP

   
PROPERTIES
    STARBASE_LOCATION : NAT1 <-> NAT1 & STARBASE_LOCATION = { 6 |-> 4 } &
    ASTEROITDS_LOCATIONS : NAT1 <-> NAT1 &
    ASTEROITDS_LOCATIONS = {3|->2, 3|->5, 5|->4, 6|->7, 7|->1, 7|->5, 7|->7, 8|-> 3, 10|->6, 11|->2, 12|-> 5} &
    STARTING_LOCATION : NAT1 <-> NAT1 & STARTING_LOCATION = {1 |-> 1} &
    X_AXIS_RANGE <: NAT1 & X_AXIS_RANGE = (1..7) &
    Y_AXIS_RANGE <: NAT1 & Y_AXIS_RANGE = (1..12) &
    SPACE_GRID : NAT1 <-> NAT1 & SPACE_GRID = Y_AXIS_RANGE*X_AXIS_RANGE &
    TRIED_TO_MOVE_SPACESHIP : NAT <-> NAT & TRIED_TO_MOVE_SPACESHIP = (0..8)*(0..13)

   
VARIABLES
    spaceShipLocation,
    spaceShipPower,
    x_coordinate, y_coordinate,
    visitedLocation,
    triedVisitPath,
    asteroidCollisionsCount
   
INVARIANT
    spaceShipLocation : POW1(SPACE_GRID) & spaceShipLocation: NAT1 <-> NAT1 &
    spaceShipPower : NAT &
    x_coordinate : NAT1 & x_coordinate <= 12 &
    y_coordinate : NAT1 & y_coordinate <= 7 &
    visitedLocation : seq(SPACE_GRID) &
    triedVisitPath : seq(TRIED_TO_MOVE_SPACESHIP) &
    asteroidCollisionsCount : NAT
   
INITIALISATION
    spaceShipLocation := STARTING_LOCATION ||
    spaceShipPower := 0    ||
    x_coordinate, y_coordinate := 1, 1    ||
    visitedLocation := [(1 |-> 1)]    ||
    triedVisitPath := [(1 |-> 1)]    ||
    asteroidCollisionsCount := 0  
   
OPERATIONS
    // Restart game or New Game
    NewGame(power) =
    PRE power : NAT1
    THEN
        spaceShipLocation := STARTING_LOCATION    ||
        spaceShipPower := power    ||
        visitedLocation := [(1 |-> 1)]    ||
        triedVisitPath := [(1 |-> 1)]    ||
        asteroidCollisionsCount := 0    ||
        x_coordinate, y_coordinate := 1, 1    
    END;
   
    response <-- spaceshipMovements =
    PRE response : SPACESHIP_MOVEMENTS_STATUS & spaceShipPower > 0
    THEN
        IF(({last(triedVisitPath)} = STARTING_LOCATION) & spaceShipPower = 0 & size(triedVisitPath) = 1)
        THEN
            response := spaceShip_locate_starting_point
        ELSIF({last(triedVisitPath)}: POW1(SPACE_GRID) & {last(visitedLocation)} /: POW1(ASTEROITDS_LOCATIONS))
        THEN
            response := successful_movement
        ELSIF({last(triedVisitPath)} /: POW1(SPACE_GRID))
        THEN
            response := reach_the_space_boundary
        ELSIF({last(triedVisitPath)} : POW1(ASTEROITDS_LOCATIONS))
        THEN
            response := reach_the_asteroid
        ELSE
            response := failed_for_some_other_reasons
        END
    END;
   
    // move up
    response <-- MoveUp =
    PRE spaceShipLocation : POW1(SPACE_GRID)
        & response : SPACESHIP_MOVEMENTS_STATUS & spaceShipLocation /= STARBASE_LOCATION
    THEN
        IF(spaceShipLocation = STARTING_LOCATION & spaceShipPower = 0 & size(visitedLocation) = 1)
        THEN
            response := game_not_start
        ELSIF(spaceShipPower < 5)
        THEN
            response := cannot_move_insufficient_power
        ELSIF({x_coordinate |-> (y_coordinate + 1)} /: POW1(SPACE_GRID))
        THEN
            triedVisitPath := (triedVisitPath <- (x_coordinate |-> (y_coordinate +1))) ||
            response := reach_the_space_boundary
        ELSIF({x_coordinate |-> (y_coordinate + 1)} : POW1(ASTEROITDS_LOCATIONS))
        THEN
            triedVisitPath := (triedVisitPath <- (x_coordinate |-> (y_coordinate +1))) ||
            visitedLocation := (visitedLocation <- (x_coordinate |-> (y_coordinate +1))) ||
            spaceShipPower := spaceShipPower - 15    ||
            asteroidCollisionsCount := asteroidCollisionsCount + 1    ||
            response := reach_the_asteroid
        ELSE
            triedVisitPath := (triedVisitPath <- (x_coordinate |-> (y_coordinate +1))) ||
            spaceShipLocation := {x_coordinate |-> (y_coordinate + 1)}    ||
            visitedLocation := (visitedLocation <- (x_coordinate |-> (y_coordinate +1))) ||
            spaceShipPower := spaceShipPower - 5    ||
            y_coordinate := y_coordinate + 1    ||
            response := successful_movement
        END    
    END;
   
    // move down
    response <-- MoveDown =
    PRE spaceShipLocation : POW1(SPACE_GRID)
        & response : SPACESHIP_MOVEMENTS_STATUS & spaceShipLocation /= STARBASE_LOCATION
    THEN
        IF(spaceShipLocation = STARTING_LOCATION & spaceShipPower = 0 & size(visitedLocation) = 1)
        THEN
            response := game_not_start
        ELSIF(spaceShipPower < 5)
        THEN
            response := cannot_move_insufficient_power
        ELSIF({x_coordinate |-> (y_coordinate - 1)} /: POW1(SPACE_GRID))
        THEN
            triedVisitPath := (triedVisitPath <- (x_coordinate |-> (y_coordinate - 1))) ||
            response := reach_the_space_boundary
        ELSIF({x_coordinate |-> (y_coordinate - 1)} : POW1(ASTEROITDS_LOCATIONS))
        THEN
            triedVisitPath := (triedVisitPath <- (x_coordinate |-> (y_coordinate - 1))) ||
            visitedLocation := (visitedLocation <- (x_coordinate |-> (y_coordinate - 1))) ||
            spaceShipPower := spaceShipPower - 15    ||
            asteroidCollisionsCount := asteroidCollisionsCount + 1    ||
            response := reach_the_asteroid
        ELSE
            spaceShipLocation := {x_coordinate |-> (y_coordinate - 1)}    ||
            triedVisitPath := (triedVisitPath <- (x_coordinate |-> (y_coordinate - 1))) ||
            visitedLocation := (visitedLocation <- (x_coordinate |-> (y_coordinate - 1))) ||
            spaceShipPower := spaceShipPower - 5    ||
            y_coordinate := y_coordinate - 1    ||
            response := successful_movement
        END    
    END;
   
    // move right
    response <-- MoveRight =
    PRE spaceShipLocation : POW1(SPACE_GRID)
        & response : SPACESHIP_MOVEMENTS_STATUS & spaceShipLocation /= STARBASE_LOCATION
    THEN
        IF(spaceShipLocation = STARTING_LOCATION & spaceShipPower = 0 & size(visitedLocation) = 1)
        THEN
            response := game_not_start
        ELSIF(spaceShipPower < 5)
        THEN
            response := cannot_move_insufficient_power
        ELSIF({(x_coordinate + 1) |-> y_coordinate} /: POW1(SPACE_GRID))
        THEN
            triedVisitPath := (triedVisitPath <- ((x_coordinate + 1) |-> y_coordinate)) ||
            response := reach_the_space_boundary
        ELSIF({(x_coordinate + 1) |-> y_coordinate} : POW1(ASTEROITDS_LOCATIONS))
        THEN
            triedVisitPath := (triedVisitPath <- ((x_coordinate + 1) |-> y_coordinate)) ||
            visitedLocation := (visitedLocation <- ((x_coordinate + 1) |-> y_coordinate)) ||
            spaceShipPower := spaceShipPower - 15    ||
            asteroidCollisionsCount := asteroidCollisionsCount + 1    ||
            response := reach_the_asteroid
        ELSE
            spaceShipLocation := {(x_coordinate + 1) |-> y_coordinate}    ||
            triedVisitPath := (triedVisitPath <- ((x_coordinate + 1) |-> y_coordinate)) ||
            visitedLocation := (visitedLocation <- ((x_coordinate + 1) |-> y_coordinate)) ||
            spaceShipPower := spaceShipPower - 5    ||
            x_coordinate := x_coordinate + 1    ||
            response := successful_movement
        END    
    END;
   
    // move left
    response <-- MoveLeft =
    PRE spaceShipLocation : POW1(SPACE_GRID)
        & response : SPACESHIP_MOVEMENTS_STATUS & spaceShipLocation /= STARBASE_LOCATION
    THEN
        IF(spaceShipLocation = STARTING_LOCATION & spaceShipPower = 0 & size(visitedLocation) = 1)
        THEN
            response := game_not_start
        ELSIF(spaceShipPower < 5)
        THEN
            response := cannot_move_insufficient_power
        ELSIF({(x_coordinate - 1) |-> y_coordinate} /: POW1(SPACE_GRID))
        THEN
            triedVisitPath := (triedVisitPath <- ((x_coordinate - 1) |-> y_coordinate)) ||
            response := reach_the_space_boundary
        ELSIF({(x_coordinate - 1) |-> y_coordinate} : POW1(ASTEROITDS_LOCATIONS))
        THEN
            triedVisitPath := (triedVisitPath <- ((x_coordinate - 1) |-> y_coordinate)) ||
            visitedLocation := (visitedLocation <- ((x_coordinate - 1) |-> y_coordinate)) ||
            spaceShipPower := spaceShipPower - 15    ||
            asteroidCollisionsCount := asteroidCollisionsCount + 1    ||
            response := reach_the_asteroid
        ELSE
            triedVisitPath := (triedVisitPath <- ((x_coordinate - 1) |-> y_coordinate)) ||
            spaceShipLocation := {(x_coordinate - 1) |-> y_coordinate}    ||
            visitedLocation := (visitedLocation <- ((x_coordinate - 1) |-> y_coordinate)) ||
            spaceShipPower := spaceShipPower - 5    ||
            x_coordinate := x_coordinate - 1    ||
            response := successful_movement
        END    
    END;
   
    // warp Drive
    response <-- WarpDrive( newposition ) =
    PRE newposition : (1..13)*(1..8) &
        response : SPACESHIP_MOVEMENTS_STATUS & spaceShipLocation /= STARBASE_LOCATION
    THEN
        IF(spaceShipLocation = STARTING_LOCATION & spaceShipPower = 0 & size(visitedLocation) = 1)
        THEN
            response := game_not_start
        ELSIF(spaceShipPower < 20)
        THEN
            response := for_warpDrive_requesting_20_power
        ELSIF({newposition} = spaceShipLocation)
        THEN
            response := space_ship_placed
        ELSIF(newposition  : ASTEROITDS_LOCATIONS)
        THEN
            triedVisitPath := triedVisitPath <- newposition ||
            visitedLocation := visitedLocation <- newposition ||
            spaceShipPower := spaceShipPower - 30    ||
            asteroidCollisionsCount := asteroidCollisionsCount + 1    ||
            response := reach_the_asteroid
        ELSIF(newposition /: SPACE_GRID)
        THEN

            response := reach_the_space_boundary
        ELSE
            spaceShipLocation := {newposition}    ||
            spaceShipPower := spaceShipPower - 20    ||
            x_coordinate := max(dom({newposition}))    ||
            y_coordinate := max(ran({newposition}))    ||
            visitedLocation := visitedLocation <- newposition ||

            response := successful_movement    
        END
    END;
   
    gameStatus, curLocation, curPowReserves, asteroidCollisions <-- MissionStatus =
    PRE gameStatus : GAME_STATUS
    THEN
        IF(spaceShipLocation = STARTING_LOCATION & spaceShipPower = 0)
        THEN
            gameStatus := Game_not_start ||
            curLocation := spaceShipLocation ||
            curPowReserves := spaceShipPower    ||
            asteroidCollisions := asteroidCollisionsCount
        ELSIF (spaceShipLocation = STARBASE_LOCATION)
        THEN          
            gameStatus := Won_the_game ||
            curLocation := spaceShipLocation ||
            curPowReserves := spaceShipPower    ||
            asteroidCollisions := asteroidCollisionsCount
        ELSIF (spaceShipLocation /= STARBASE_LOCATION & spaceShipPower < 5)
        THEN
            gameStatus := You_lost_the_game   ||
            curLocation := spaceShipLocation ||
            curPowReserves := spaceShipPower    ||
            asteroidCollisions := asteroidCollisionsCount
        ELSE
            gameStatus := Game_not_over   ||
            curLocation := spaceShipLocation ||
            curPowReserves := spaceShipPower    ||
            asteroidCollisions := asteroidCollisionsCount
        END
    END;
   
   
   
    visited <-- RegionsVisited =
    BEGIN
        visited := visitedLocation
    END;
   
    rest <-- yourRestNormalMovement =
    BEGIN
        IF(spaceShipPower >= 5)
        THEN
            rest := spaceShipPower / 5
        ELSE
            rest := 0
        END
    END;
   
    rest <-- yourRestWarpDriveMovement =
    BEGIN
        IF(spaceShipPower >= 20)
        THEN
            rest := spaceShipPower / 20
        ELSE
            rest := 0
        END

    END
END
