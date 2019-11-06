open util/boolean

abstract sig User{}

sig LoggedUser extends User{
    fiscalCode: one String,
    username: one String,
    password: one String,
    banned: one Bool,
    numOfSubmissions: one Int,
    badReports: one Int,
    topUser: one Bool
}
{
    topUser = True iff numOfSubmissions >= 50 and
    banned = True iff badReports >= 3
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
    isSafe: one Bool,
    numberOfViolations: one Int,
    areas: set Area,
    streets: set Street
}

sig Area {
    isUnsafeArea: one Bool,
    streetsOfArea: set Street
}

sig Street {
    inCity: one String,
    isSafe: one Bool
}

sig Plate{
    egregiousOffender: one Bool,
    numberOfInfraction: one Int,
    platenumber: one String
}

sig Position {
    geoTag: one String,
    city: one City,
    area: one Area,
    street: one Street
} 

sig Picture{
    timeStamp: one String,
    pictureId: one String
}

// There must not be two different user with the same username
fact NoDoubleUsername{
    no disjoint u1, u2: LoggedUser | u1.username = u2.username
}

// There must not be two different users with the same fiscal code
fact NoDoubleFiscalCode{
    no disjoint u1, u2: LoggedUser | u1.fiscalCode = u2.fiscalCode
}

// A banned user can't send a report
fact NoValidReportByBannedUser{
    all r:Report | r.validReport = True implies r.uploadedBy.banned != True
}

// An invalid report can't have the same id as a violation. In other words an invalid report can't become a violation
fact NoViolationGeneratedByInvalidReport{
    no v: Violation, r: Report | r.validReport = False and v.violationId = r.reportId
}

// A valid report must have the same id of the corresponding violation
fact ReportToViolation {
    all r: Report | r.validReport = True implies
                    some v: Violation | r.reportId = v.violationId
}

// A street is considered unsafe if there are at least 10 violations in that street
fact UnsafeStreet {
    all s: Street | s.isSafe = False iff (some v: Violation | v.position.street = s and #v >= 10)
}

// An Area is considered unsafe if there are at least 4 streets of that area that are considered unsafe
fact UnsafeArea {
    all a: Area | a.isSafe = False iff (some s: Street | a.street = s and #s >= 4)
}

// A plate (representing a driver) becomes an "egregious offender" if the number of violations
// associated to its plate number becomes greater than 10
fact EgregiousOffender{
    all p: Plate | p.egregiousOffender = True iff p.numberOfInfraction > 10
}
// All violations must be associated  to a Plate
fact NoEmpyPlate{
    all v: Violation | some p: Plate | v.committedBy in p
}

// All violations must be associated  to logged user who uploaded it
fact NoEmpyPlate{
    all v: Violation | some l: LoggedUser | v.uploadedBy in l
}

// There must not be two valid reports of the same violation simultaneously
assert NoUbiquitousSubmissionsOfSamePlate{
    no disjoint r1, r2: Report | r1.validReport = True and r2.validReport = True
                                and r1.reportId != r2.reportId
                                and r1.timeStamp = r2.timeStamp 
                                and r1.committedBy.platenumber = r2.committedBy.platenumber
                                
}
check NoUbiquitousSubmissionsOfSamePlate for 5

// There must not be two valid reports by the same user simultaneously
assert NoUbiquitousSubmissionsBySameUser{
    no disjoint r1, r2: Report | r1.validReport = True and r2.validReport = True
                                and r1.reportId != r2.reportId
                                and r1.timeStamp = r2.timeStamp 
                                and r1.uploadedBy.username = r2.uploadedBy.username
                                
}
check NoUbiquitousSubmissionsBySameUser for 5

// There must not be bad correspondence between the report and the corresponding approved violation 
assert NoBadCorrespondence{
    no r: Report, v: Violation | (r.uploadedBy.username != v.uploadedBy.username
                                or r.timeStamp != v.timeStamp
                                or r.position.geoTag != v.position.geoTag
                                or r.pictureId != v.picture.pictureId)
                                and r.reportId = v.violationId
}
check NoBadCorrespondence for 5



pred show{ 
    #Report = 4
    #LoggedUser = 4
    #Area = 4
    #Street = 20
    #Plate = 10
    #Violation = 2
    #Position = 20
    #Picture = 5
    some u:LoggedUser | u.banned = True
}
run show for 10 but exactly 2 City