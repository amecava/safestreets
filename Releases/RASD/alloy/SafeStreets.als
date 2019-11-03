open util/boolean

abstract sig User{}

sig LoggedUser extends User{
    fiscalCode: one String,
    username: one String,
    password: one String
}

sig GuestUser extends User{
    userId: one String
}

sig Violation{
    position: one Position,
    type: one Type,
    plate: one Plate
}

sig Plate{
    platenumber: one String
}

sig Type{

}

sig Position {
    geoTag: one String
} 

sig Picture{

}

sig GIS {

}

sig Municipality {

}




