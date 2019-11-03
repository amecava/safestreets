open util/boolean

abstract sig User{}

sig LoggedUser extends User{
    fiscalCode: one String,
    username: one String,
    password: one String,
    banned: one Bool
}

sig GuestUser extends User{
    userId: one String
}

sig Violation{
    violationId: one String,
    uploadedBy: one User,
    committedBy: lone Plate,
    picture: one Picture,
    timeStamp: one String,
    position: one Position,
    type: set String,
    plate: one String
}
{
    #this.type >= 1
}

sig Report {
    reportId: one String,
    uploadedBy: one User,
    picture: one Picture,
    timeStamp: one String,
    position: one Position,
    type: set String,
    plate: lone Plate,
    validReport: one Bool
} 
{
    #this.type >= 1
}

sig City {
    name: one String,
    area: set Area,
    streets: set Street
}

abstract sig Statistics{}

sig CityStatistics extends Statistics {
    cityCodeName: one City,
    infactions: set Violation,
}

sig Area {
    isUnsafeArea: one Bool,
    unsafeStreets: set Street
}

sig Street {
    inCity: one String
}

sig Plate{
    platenumber: one String
}

sig Position {
    geoTag: one String
} 

sig Picture{
    timeStamp: one String
}

fact NoDoubleUsername{
    no disjoint u1, u2: LoggedUser | u1.username = u2.username
}

fact NoDoubleFiscalCode{
    no disjoint u1, u2: LoggedUser | u1.fiscalCode = u2.fiscalCode
}

fact NoValidReportByBannedUser{
    all r:Report | r.validReport = True implies r.uploadedBy.banned != True
}

fact NoTwoUbiquitousSubmissionsOfSamePlate{
    no disjoint r1, r2: Report | r1.validReport = True and r2.validReport = True
                                and r1.timeStamp = r2.timeStamp 
                                and r1.committedBy.platenumber = r2.committedBy.platenumber
                                and r1.position != r2.position
}

fact NoViolationGeneratedByInvalidReport{
    no v: Violation, r: Report | r.validReport = False and v.violationId = r.reportId
}

