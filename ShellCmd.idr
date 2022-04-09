module ShellCmd

data Access = LoggedOut | LoggedIn

data PwdCheck = Correct | Incorrect

data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
     Password : String -> ShellCmd PwdCheck LoggedOut
                          (\pwdCheck => case pwdCheck of
                                             Correct => LoggedIn
                                             Incorrect => LoggedOut)
     Logout : ShellCmd () LoggedIn (const LoggedOut)
     GetSecret : ShellCmd String LoggedIn (const LoggedIn)

     PutStr : String -> ShellCmd () state (const state)
     Pure : (res : ty) -> ShellCmd ty (f res) f
     (>>=) : ShellCmd a state f ->
             ((res : a) -> ShellCmd b (f res) f') ->
             ShellCmd b state f'

session : ShellCmd () LoggedOut (const LoggedOut)
session = do
  Correct <- Password "wurzel"
    | Incorrect => PutStr "Wrong password"
  msg <- GetSecret
  PutStr ("Secret code: " ++ show msg ++ "\n")
  Logout
