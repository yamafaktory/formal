namespace Run

structure Message where
  severity : List Char
  data : List Char
deriving DecidableEq

def realErrors (isSorryDeclaration : List Char → Bool) (messages : List Message) :
    List Message :=
  messages.filter fun message =>
    message.severity == "error".toList && !isSorryDeclaration message.data

def promotedSorries (hasSorry : List Char → Bool) (messages : List Message) : List Message :=
  (messages.filter fun message => message.severity == "warning".toList && hasSorry message.data).map
    fun message => { message with severity := "error".toList }

def errors (isSorryDeclaration hasSorry : List Char → Bool) (messages : List Message) :
    List Message :=
  realErrors isSorryDeclaration messages ++ promotedSorries hasSorry messages

def success (code : Option Int) (errors : List Message) : Bool :=
  code == some 0 && errors.isEmpty

def parse_output_a_sorry_warning_is_never_a_success : Prop :=
  ∀ isSorryDeclaration hasSorry messages code message, message ∈ messages →
    message.severity = "warning".toList → hasSorry message.data = true →
    success code (errors isSorryDeclaration hasSorry messages) = false

def parse_output_every_promoted_sorry_is_reported_as_an_error : Prop :=
  ∀ hasSorry messages message, message ∈ promotedSorries hasSorry messages →
    message.severity = "error".toList

def parse_output_the_first_error_lean_reported_stays_first : Prop :=
  ∀ isSorryDeclaration hasSorry messages, realErrors isSorryDeclaration messages ≠ [] →
    (errors isSorryDeclaration hasSorry messages).head? =
      (realErrors isSorryDeclaration messages).head?

def parse_output_a_nonzero_exit_is_never_a_success : Prop :=
  ∀ code errors, code ≠ some 0 → success code errors = false

end Run
