% build using
%    lhs2TeX GuabaoPaper.lhs | pdflatex --jobname=GuabaoPaper

\documentclass[runningheads]{llncs}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include GCL.fmt
%include lineno.fmt

\include{macros}

\renewcommand*{\formatlinenum}[1]{\makebox[3em][l]{\scriptsize{#1}}}%

\numbersoff

\newcommand{\todo}[1]{{\bf Todo}: \lbrack #1 \rbrack}

\newcommand{\sshotimg}[1]{
\adjustbox{padding*=2ex 8ex 2ex 8ex, max width=\textwidth}{%
\includegraphics{img/#1.jpg}}}

\begin{document}

\title{Imperative Program Derivation in Guabao
%\thanks{Supported by organization x.}
}

\author{Shin-Cheng Mu\inst{1}%\orcidID{0000-0002-4755-601X}
\and
Ting-Yan Lai\inst{1}\and
Thing-Han Lim\inst{1}\and
Chien-Yuan Su\inst{1}\and
Hsien-En Tzeng\inst{2}%
}
%
\authorrunning{S-C. Mu  et al.}

\institute{
%Institute of Information Science, %\\
Academia Sinica, Taiwan \and
National Taiwan University, Taiwan
}


\maketitle              % typeset the header of the contribution
%
\begin{abstract}
Guabao is an integrated environment for imperative program derivation --- the process of formally and step-wise constructing a program from its specification.
As the programmer types in the code, in a variation of Guarded Command Language,
Guabao computes its proof obligations in an interface that encourages the program and its correctness proof to be developed hand in hand.
We present the user experience of Guabao, the algorithm it uses to compute proof obligations and infer pre/postconditions, and compare it with contemporary tools serving similar purposes.
\keywords{program derivation \and integrated developing environment \and proofs}
\end{abstract}

\section{Introduction}

\begin{quote}
\ldots to prove the correctness of a given program was in a sense putting the cart before the horse. A much more promising approach turned out to be letting correctness proof and program grow hand in hand: with the choice of the structure of the correctness proof one designs a program for which this proof is applicable. The fact that then the correctness concerns turn out to act as an inspiring heuristic guidance is an added benefit.
\begin{flushright}
--- E. W. Dijkstra, 1973. \cite{Dijkstra:74:Programming}
\end{flushright}
\end{quote}

\emph{Program derivation} is the process of formally and step-wise constructing a program from its specification, such that every step is mathematically justifiable. As a methodology to construct reliable software, its central idea is that, rather than verifying a program after it has been written, \emph{a program and its correctness proof should be developed hand in hand}.
This does not necessarily imply more work for the programmer.
On the contrary, as argued in the quote above, thinking about how a program can be proven correct often gives useful hints on how to construct the program.

Theories of imperative program derivation based on the \emph{weakest precondition} calculus was initially developed by Dijkstra~\cite{Dijkstra:75:Guarded}.
It can be seen as a variation of Hoare logic~\cite{Hoare:69:Axiomatic} where, instead of a more conventional operational semantics, the meaning of a program is taken to be a \emph{predicate transformer}: a function that, given a desired postcondition $Q$, yields the weakest precondition $P$ such that the program will terminate in a state that satisfies $Q$.
This view of programs invites the programmer to abstract away from how the program operationally carries out its task, and instead to focus on the postcondition that the programmer wants to achieve.
The program is then derived by manipulating the pre/postconditions using various calculational rules.
Various previous work~\cite{Dijkstra:76:Discipline,%
Gries:81:Science,Kaldewaij:90:Programming,Morgan:90:Programming,%
Backhouse:03:Program,Backhouse:11:Algorithmic} collectively developed a methodology of program development from specification, equipped with techniques for constructing a loop invariant from a desired postcondition, constructing the loop body from its last step, ensuring termination, etc.
This methodology was applied to derive algorithms solving individual small problems
(e.g~\cite{Rem:89:Small,Rem:90:Small}) as well as families of problems (e.g~\cite{Zantema:92:Longest}).
% Meanwhile, derivation of functional programs, a closely related topic, has also been developing (e.g~\cite{Bird:10:Pearls}).
Within the advocating community it is at least wished that the concept of program derivation should be taught as part of the fundamental training for programmers and computing science majors.
% These days, program derivation is more practiced in the functional programming community. Derivation of imperative programs, however, is also a field with rich possibilities and potentials.

Since 2011, the first author has been teaching an undergraduate level Programming Languages course, in which imperative program derivation is covered.
From the experiences accumulated, we felt that such a course would benefit from having a supporting tool.
Therefore we created Guabao.
The aim is to develop a programming environment having the following features:
\begin{enumerate}
\item It encourages {\bf developing proofs and programs together}.
While the user may certainly write up all the code in Guabao and verify it afterwards, the interface shall encourage the user to interleave proving and coding, and let the two modes aid each other.
\item It encourages {\bf backward-reasoning}.
Since it is easier to construct the weakest precondition of an assignment (|x := e|) from its postcondition than the other way round,
to construct a block of statements, many derivation techniques start with thinking about what the \emph{last assignment} could be.
The interface of Guabao should make such construction easy and natural.
\item It allows {\bf free-form text editing}, as opposed to treating programs as diagrams as some program construction tools do, since we believe it what most programmers would prefer.
\end{enumerate}
In Section~\ref{sec:programming-example} we will see an example demonstrating all these features.
It might also help to clarify what Guabao is not:
\begin{enumerate}
\item Gaubao is not an implementation of Guarded Command Language (GCL).
Dijkstra~\cite{Dijkstra:98:Cruelty} wrote that he would
design a programming language for teaching (which we believe would be GCL) and ``see to it that [it] has not been implemented on campus so that students are protected from the temptation to test their programs.''
Gaubao is not an implementation of GCL in which one can write a program and test it, but an environment where a program and its proof can be designed together.
% One cannot yet execute the program --- although it is not difficult to implement an interpreter and allow a program to run once all proofs are done.
\item Guabao does not intend to prove \emph{everything} regard the correctness of the program for the user.
Instead, it computes the proof obligations needed to guarantee correctness, and let them guide the development of the said program.
Guabao does employ an SMT solver (currently Z3~\cite{MS:12:Z3}) to discharge simple proof obligations.
However, we believe that proving properties that are related to the algorithmic aspect of a program and, in case of failure, learning from the proof how the program should evolve to allow the proof to go through, is a part of the program development process, which should be carried out by the user.
It is especially so in a course teaching program derivation.
Currently Guabao does not check user-written proofs.
To do so we need to develop a representation of equational proofs, which is one of our future works.
\end{enumerate}

Guabao is implemented as an extension of the editor Visual Studio Code,
which can be installed by searching for the extension "Guabao" in the editor, or through its Extensions Marketplace~\footnote{\url{https://marketplace.visualstudio.com/items?itemName=scmlab.guabao}}.
A simple one-click installation downloads the frontend and the pre-compiled backend.%
~\footnote{Z3 has to be installed separately, however.}
%The readers are welcomed to give it a try!
The backend of Guabao is implemented using Haskell~\cite{PeytonJones:03:Haskell}, while the frontend is implemented using Reason~\cite{Walke:16:Reason} and compiled to Javascript to run in VS Code.
Regarding its name,
GUA in Guabao comes from GUArded command language.
Guabao (\cjk{??????}) is a street food popular in places including Taiwan, where Guabao the software was designed.

After giving a brief review of the Guarded Command Language in Section~\ref{sec:gcl}, we demonstrate how it is like using Guabao by a simple example in Section~\ref{sec:programming-example}.
Section~\ref{sec:po-generation} presents the algorithm we use to generate proof obligations and infer pre/postconditions of specs.
We compare Guabao with some other tools in Section~\ref{sec:related-works}
before we conclude in Section~\ref{sec:conclude}.

\section{The Guarded Command Language}
\label{sec:gcl}

%format (MANY (x)) = "{" x "}^{*}"
%format (SOME (x)) = "{" x "}^{+}"
\begin{figure}[t]
\begin{spec}
Prog   ::=  (MANY Decl) (MANY Stmt)
Decl   ::=  VAR (SOME Var) : Type ?{-"\!"-}(assert Expr) | CON (SOME Var) : Type ?{-"\!"-}(assert Expr)
Stmt   ::=  (assert Expr) | skip | abort | SOME Var := SOME Expr
       |    DO (MANY GdCmd) OD | IF (MANY GdCmd) FI
GdCmd  ::=  Expr -> SOME Stmt
\end{spec}
\caption{An abstract syntax of Guarded Command Language.
|Var| denotes the collection of variable identifiers.
Definitions of |Expr| and |Type| are omitted.}
\label{fig:gcl-syntax}
\end{figure}

Guabao uses a variation of the Guarded Command Language (GCL)~\cite{Dijkstra:75:Guarded},
which we will briefly review in this section,
emphasising on what needs to be proved about a given statement.
A condensed presentation of its abstract syntax is given in Figure~\ref{fig:gcl-syntax}.
A program consists of a section of declarations followed by a section of statements.
Constant and variable declarations respectively start with keywords |VAR| and |CON|.
They can be accompanied by an optional assertion stating properties we assume about the declared entities.

An assertion is a Boolean-valued expression in curly brackets.
By the convention of the program derivation community, a \emph{Hoare triple} |htriple P S Q| denotes total correctness: that is, the program |S|, when executed in a state satisfying |P|, \emph{terminates} in a state satisfying |Q|.
We prefer it over the partial correctness interpretation (that is, |S| establishes |Q| \emph{if} it terminates) because, as we will see in Section~\ref{sec:programming-example}, that the program must terminate provides useful hints about how it can be written.
% The notation |[!pre, post!]| denotes a \emph{spec} --- a hole yet to be filled in with code that shall establish the postcondition |post| provided that precondition |pre| is satisfied.

% For example, the following is an unfinished program that, upon exit, stores the value of |A * B| in |r|, provided that both |A| and |B| are non-negative.
% \begin{spec}
% CON A, B : Int (assert (A >= 0 && B >= 0))
% VAR r : Int
%
% [: A >= 0 && B >= 0, r = A * B :]
% \end{spec}

The statement |skip| does nothing, while |abort| simply aborts the program.
The operator |:=| denotes assignment; parallel assignment of multiple variables is allowed.
A \emph{guarded command} |B -> S|, where |B| is a Boolean-valued expression, denotes a command where |S| is executed only if the \emph{guard} |B| evaluates to |True|.

Guarded commands alone do not form a complete statement.
The statement |IF ... FI|, enclosing a group of guarded commands, denotes conditional branches.
For example, |IF B0 -> S0 || B1 -> S1 FI| has two branches, where |S_i| is executed if |B_i| holds (|i `elem` {0,1}|).
If both |B0| and |B1| holds, \emph{one} of the branches is nondeterministically executed.
If neither holds, the program aborts.
To prove that
\begin{spec}
htriple P (IF B0 -> S0 | B1 -> S1 FI) Q {-"~~,"-}
\end{spec}
one has to prove that 1. |htriple (P && Bi) Si Q| for |i `elem` {0,1}| --- both branches establish |Q| if executed, and 2. that |P ==> B0 |||| B1| --- such that the program would not abort.

A group of guarded commands surrounded by |DO ... OD| denote a while-loop.
In |DO B0 -> S0 || B1 -> S1 OD|, for example, when either |B0| or |B1| holds, the corresponding statement |S0| or |S1| gets executed, before we attempt at the next iteration. When neither holds, the loop exits.
In our methodology of program construction,
each loop must have an \emph{invariant} --- a property that shall always hold at the beginning of the loop, and a \emph{bound} --- a value that strictly decreases after each iteration of the loop.
This is denoted by
\begin{spec}
htriple (P, BND: e) (DO B0 -> S0 | B1 -> S1 OD) Q
\end{spec}
where |P| is the loop invariant, |e| the bound, and |Q| the postcondition.

Once we introduce such a loop, however, we have also given ourselves \emph{four} proof obligations:
\begin{spec}
{-"\mbox{1. \sf InvBase}:\qquad"-}   P && not (B0 || B1) ==> Q {-"~~,"-}
{-"\mbox{2. \sf InvInd}:\qquad"-}    htriple (P && Bi) Si P {-"\mbox{,~~for~}"-} i `elem` {0,1} {-"~~,"-}
{-"\mbox{3. \sf TermBase}:\qquad"-}  P && (B0 || B1) ==> e >= 0 {-"~~,"-}
{-"\mbox{4. \sf TermInd}:\qquad"-}   htriple (P && Bi && e = C) Si (e < C) {-"\mbox{,~~for~}"-} i `elem` {0,1} {-"~~."-}
\end{spec}
Properties {\sf InvBase} and {\sf InvInd} guarantee that the loop is partially correct: that is, if the loop terminates at all, it terminates in a state satisfying |Q|.
{\sf TermBase} and {\sf TermInd} establish that the loop does terminate.
The four properties together guarantee total correctness.

One can imagine that, as the size of program grows, the number of proof obligations (abbreviated to POs) may soon grows out of hand.
\footnote{With proper use of assertions, the size of proof obligations can be limited to be linear in the size of the program \cite{Dijkstra:69:Understanding}. Still, that is a lot of properties to prove.}
It happens often that some of the properties are rather routine, but they still need to be proved.
It would be nice to have an environment that keeps tracks of these POs.
Even better, the environment shall encourage the idea that programs can be designed around having to discharge these POs.
Therefore the proofs are no longer additional burden, but useful guides during program development.

\section{Programming in Guabao}
\label{sec:programming-example}

In this section we demonstrate the user experience of program development in Guabao.
As our worked example, consider a classical exercise: given natural numbers |A| and |B|,
compute |A * B| using only addition, subtraction, predicates |even| and |odd|, and multiplication and division by |2|.
% This is a classical exercise, and was once a useful one for early microcomputers, which did not have an atomic instruction for general multiplication (multiplication by |2| involves only bit-shifting and is much cheaper).

Specification of the problem is shown below.
We declare two constants |A| and |B|, about them all we know is that |B| is non-negative.
%(as asserted in |assert (A >= 0 && B >= 0)|).
Functions |even| and |odd|, which we will use later,
are declared as constants.
Also declared is a variables |r| having type |Int|.
The goal of the program is to store the value of |A * B| in variable |r|, as stated in |assert (r = A * B)| --- a valid Guabao program must end with an assertion stating its postcondition.
The question mark indicates code yet to be written.
\begin{spec}
CON A, B : Int (assert (B >= 0))
CON even, odd : Int -> Bool
VAR r : Int

?
(assert (r = A * B))
\end{spec}

% \begin{figure}[t]
% \includegraphics[width=\textwidth]{img/sshot00.jpg}
% \caption{Fast Multiplication in Guabao.}
% \label{fig:fastmul}
% \end{figure}

Guabao parses and analyses the code as it is typed into the editor.
Once the code is entered, we will see:\\
\sshotimg{sshot00}\\
Guabao automatically expands the question mark |?| to a \emph{spec} ??? a hole in the program to be filled in, denoted by |[! ... !]|.
The idea of a spec is inspired by Morgan~\cite{Morgan:90:Programming}, with a slight difference: in Morgan~\cite{Morgan:90:Programming} one starts program construction from a spec with given pre/postconditions, while in Guabao the pre/postconditions are inferred.
The interface shows, on line 5 and 7, that code to be filled in shall bring the state of the system from precondition |True| to postcondition |r = A * B|. Properties of global constants (namely |B >= 0|) are universally true and implicitly conjuncted with all assertions. They are displayed separately in a ``Property'' section in the right pane.

\paragraph{Introducing a Loop}
For such a non-trival task we expect that a loop is needed,
so we try to fill in the spec:
\\\sshotimg{sshot01}\\
Guabao syntactically enforces that each loop comes with a loop invariant and a bound.
Various techniques were developed to construct candidates of loop invariants from the postcondition.
We cannot properly cover all the techniques in this paper but, for interested readers, we recommend Kaldewaij~\cite{Kaldewaij:90:Programming}.
For this problem, we use one of the standard tricks:
choosing |a * b + r = A * B| as the loop invariant (line 7), which can be established by initialisation |a, b, r := A, B, 0| (line 6).
By letting the guard be |b /= 0| (line 8), the proof obligation {\sf InvBase} instantiates to |a * b + r = A * B && b = 0 ==> r = A * B|, which is trivial to prove.
Now that the loop terminates when |b = 0|, a strategy would be to keep decreasing |b| in the loop body until it reaches |0|.
Therefore we let |b| be the bound (line 7).
The loop body is left as a question mark.

When the cursor is in the spec, press {\tt ctrl-c-r} to fill in the spec.
In the screenshot in Figure~\ref{fig:sshot2}, the code typed into the hole becomes part of the program,
while the question mark becomes a new hole.
\footnote{This style of interaction (including the hot-key combination) is inspired by Agda.}
The two POs shown on the right pane are respectively calculated {\sf InvBase} and {\sf TermBase}, while the pre/postconditions of the spec are calculated from {\sf InvInd}.
%\\\sshotimg{sshot02}\\

\begin{figure}[t]
\sshotimg{sshot02}\\
%\sshotimg{sshot03}
\caption{After introducing a loop.}
\label{fig:sshot2}
\end{figure}

\paragraph{The Interface}
Let us get a closer look at the interface of Guabao.
%Now it is a good time to inspect the interface of Guabao.
In the program in the left pane,
blue shade in the code indicates ``there are proof obligations incurred here.''
Program locations associated with more POs get thicker shades.
The right pane contains information including
\begin{itemize}
\item inferred POs,
\item pre/postconditions of specs,
\item global properties, etc.
\end{itemize}
Since the number of POs can be large, in the right pane we display those on the path of the current location of the cursor.
In Figure~\ref{fig:sshot2}, the cursor is at line 7, beginning of the loop.
POs in the right pane include:
\begin{spec}
a * b + r = A * B  && not  (b /= 0)   ==>  r = A * B  {-"~~, \mbox{which is {\sf InvBase}, and}"-}
a * b + r = A * B  &&      b /= 0     ==>  b >= 0     {-"~~, \mbox{which is {\sf TermBase}}."-}
\end{spec}
%The first one is aforementioned {\sf InvBase}, while the second is {\sf TermBase}.

The PO labelled {\sf InvBase} is trivial to prove --- the invariant and the bound were designed to make it trivial.
At the top of the box displaying this PO there is a icons of a magic wand.
Clicking on it invokes the SMT solver Z3, which generates the output "Q.E.D.", indicating that it is proved.
The PO labelled {\sf TermBase}, however, turns out to be falsifiable. Indeed, the premise does not guarantee |b >= 0|! We thus realise that we need a stronger invariant. The new invariant would be:
\begin{spec}
 a * b + r = A * B  &&  b >= 0 {-"~~."-}
\end{spec}
After the user updates the invariant, the POs and the specs are updated accordingly.


\paragraph{Constructing the Loop Body}
Now we attempt to construct the loop body.
Having {\sf TermInd} in mind, one of the objective of the loop is to decrease the bound |b| and thereby construct a loop that terminates.
There are various ways to do so.
One may decrement |b| by |b := b - 1|, or one may divide |b| by half --- knowing that |b| is not zero.
Let us try the second way. We type
\begin{spec}
?
b := b / 2
\end{spec}
into the spec.
In effect, we are trying to construct a block of statements by guessing that the \emph{last} statement could be |b := b / 2|, and think about what should come before it.
Note that the operator |/| here denotes integral division, which rounds down to the closest integer.
Pressing {\tt ctrl-c-r}, the question mark gets expanded to a spec with an updated postcondition (top of Figure~\ref{fig:sshot45}).
The spec expects us to fill in some code that brings the computer from a state satisfying
\begin{spec}
a * b + r = A * B && b >= 0 && b /= 0
\end{spec}
to a state satisfying
\begin{spec}
a * (b / 2) + r = A * B && b / 2 >= 0 {-"~~."-}
\end{spec}
What can we do?

\begin{figure}[th]
\sshotimg{sshot04}\\
\sshotimg{sshot05}
\caption{Top: guessing that the last statement could be |b := b / 2|.
Bottom: trying to fill in |b := b * 2| in the loop body --- we cannot prove the PO.}
\label{fig:sshot45}
\end{figure}

One possibility is filling in |b := b * 2|.
That, however, results in the bottom of Figure~\ref{fig:sshot45}, where the PO shown in the right pane, which is a consequence of {\sf TermInd} demands us to prove that
%format bnd_0 = "{?bnd_{51}}"
\begin{spec}
.... b = bnd_0 ... ==> (b * 2) / 2 < bnd_0 {-"~~,"-}
\end{spec}
where |bnd_0| is a system-generated logical variable.
This property cannot be proved, and
we learn that |b := b * 2; b := b / 2| is a bad idea as the loop body --- the bound |b| does not decrease.

Another possible choice is |a := a * 2|. If we try this option:\\
\sshotimg{sshot06}\\
It turns out that we have to prove a PO that is essentially
\begin{spec}
(a * b) + r = A * B .... {-"~~"-}  ==> {-"~~"-} ((a * 2) * (b / 2)) + r = A * B ....
\end{spec}
This time we demonstrate a manual proof.
Each PO comes with a hash key.
Clicking on the hash key ({\sf \#5F2E722} in the screenshot above) for the PO creates
a new comment block labelled by the hash key, in which the programmer can write
up a proof of the corresponding property.
Hash key of a PO having a proof block is displayed in blue.
A program is proven correct if all POs are proved either by Z3 or by the programmer.

Currently the system makes no attempt to check the proofs written by the user ---
in a lecture the proofs would be checked by a teacher.
It is our future work to develop a language that is suitable for manual calculational proofs and yet machine-verifiable.

% They are just comments for the user.
% Hash key of a PO with a proof block is displayed in blue (see the top-right corner).
%

It turns out that, to prove the PO, we will need |b| to be a even number (line 17 in the screenshot), assuming integral division.
This is a hint that we shall wrap |a := a * 2; b := b / 2| in a guard |even b|, to ensure that |b| is even, and put it in an |IF| construct.
The current code is:
\begin{spec}
DO b /= 0 ->
  IF even b ->  a := a * 2
                b := b / 2
  FI
OD {-"~~."-}
\end{spec}

\paragraph{Totalisation}
We are not done yet. Among all the POs we will be asked to prove that |IF| is total --- every possible case is covered.
Therefore we need to think about what to do in the |odd b| case. For this case we might decrease |b| using |b := b - 1|. By a similar process we can construct what to do with |a| and |r| in this case to maintain the invariant. A possible final program would be (omitting the declarations):
\begin{spec}
a, b, r := A, B, 0
(assert (a * b + r = A * B && b >= 0, bnd: b))
DO b /= 0 ->  IF  even b  ->  a := a * 2
                              b := b / 2
              |   odd b   ->  r := a + r
                              b := b - 1
              FI
OD
(assert (r = A * B)) {-"~~,"-}
\end{spec}
which computes |A * B| using $O(\log B)$ atomic arithmetic operations.

But that is not the only possible program. One might decide to do nothing in the |odd b| case and always decrease |b| regardless of its parity, resulting in:

\begin{spec}
a, b, r := A, B, 0
(assert (a * b + r = A * B && b >= 0, bnd: b))
DO b /= 0 ->  r := a + r
              b := b - 1
              IF  even b ->  a := a * 2
                             b := b / 2
              |   odd b ->   skip
              FI
OD
(assert (r = A * B)) {-"~~."-}
\end{spec}
The program is correct as long as one can prove all the POs.

\paragraph{Summary}
Let us recapitulate the interaction between a program and its proof in this example.
Certainly, the program determines what ought to be proved --- introducing a statement also introduces corresponding POs.
Meanwhile, these POs gave hints on how to proceed with program construction.
One may design the program --- for example, choosing the loop guard or choosing a method to decrease the bound --- such that some POs are trivial to discharge.
Pre/postconditions of a spec, inferred from future POs, shows what a piece of code is supposed to do.
By observing what is missing in an attempted proof, one may learn how to strengthen the loop invariant, to enclose the program fragment in a guard, or learn that the current choice is simply wrong.
The interface of Guabao aims to encourage such interaction.

% \begin{figure}
%   \centering
%      \begin{subfigure}[b]{0.3\textwidth}
%        here
%        \caption{$y=x$}
%      \end{subfigure}
%      \begin{subfigure}[b]{0.3\textwidth}
%        there
%        \caption{$y=x$}
%      \end{subfigure}
% \end{figure}


\begin{figure}[th]
\sshotimg{mss}
\caption{The \emph{maximum segment sum} problem.}
\label{fig:mss}
\end{figure}

\paragraph{Other Features}
Figure~\ref{fig:mss} presents the classical \emph{maximum segment sum} problem, which demonstrates some features we have not mentioned in the previous example.
Given an array of |N| integers (line 2), the goal is to find the maximum possible some of a consecutive segment.
The postcondition on line 17 formally describes the goal --- notice the use of Eindhoven notation for quantification, which denotes ``for |0 <= i <= j <= N|, collect |sum i j| and find the largest |(`max`)|,  where |i| and |j| are bound variables.''
Guabao supports arrays that can be nested and mutable (if declared in |VAR|).
Pure functions to be used in assertions can be defined in declaration blocks |{: ... :}| (line 5 -- 7 in Figure~\ref{fig:mss}).
Shown in the right pane is a PO induced from {\sf InvInd} --- that the invariant holds after one more iteration of the loop.
The notation |P (subst s (s `max`r))| denotes substituting |s `max`r| for all free occurrences of |s| in |P|, which appears in the PO as a consequences of |s := s `max` r| in the code. Clicking on |P| expands its definition and performs the substitution.

Like the previous example, development of this program was not done in one step.
The usual story goes like: we started with a spec without |r|, using |P n  && 0 <= n <= N| as the loop invariant, and the first attempt was to construct the main loop with |n := n + 1| as its \emph{last} step. While trying to satisfy the spec and prove {\sf InvInd}, we would discover that, to update |s| quickly, we may strengthen the invariant with a variable |r|, storing the maximum \emph{suffix} sum, as stated by |Q n|, which was also discovered during the proof. The interface of Guabao wishes to make this process natural and smooth.

\section{Behind the Scenes}
\label{sec:po-generation}

A central part of the backend of Guabao is an engine that scans through the code, generates a collection of POs, and infers the pre/post conditions of specs.
In this section we examine the design of this engine.

When seeing a Hoare triple |htriple P S Q|, Guabao invokes the ternary function |struct _ _ _|, summarised in Figure~\ref{fig:struct}, to generate POs.
The function |struct _ _ _| will be discussed in more details later.
To understand it, however, we shall start with some discussion on the interplay between assertions and POs.
%\todo{Briefly describe the relation of wp, assertions and PO}
%something like: "The algorithm generating POs is described below: it involves the concept of weakest precondition and how the programmer places the assertions among the program"
%SCM: but that's what I am going to discuss. I added a sentence: The function |struct _ _ _| will be discussed in more details later.


\paragraph{Weakest preconditions}
It is known that for every statement |S|, one can compute |wp S Q|, its weakest precondition with respect to postcondition |Q|.
Our definition of |wp| is shown in Figure~\ref{fig:wp}.
The first few cases are standard: |wp abort Q| is always |False|, |wp skip| is the identity function, and |wp (x := e)| is substitution --- |Q (subst x e)| denotes substituting all free occurrences of |x| in |Q| by |e|.
The cases for |if| and |do| statements are also standard --- for clarity we present instances containing two guarded commands.

A sequence of statements |S0; ..; Sn| operationally denotes performing the statements in the given order.
We extend the notion to allow assertions and specs in the sequence.
In the patterns between line \ref{code:wp:seq:0} -- \ref{code:wp:seq:3} in Figure~\ref{fig:wp},
|({P} Ss)| denotes a sequence starting with an assertion,
|(eSpec Ss)| denotes one starting with a spec,
and |(s; ss)| a sequence starting with a non-sequent statement followed by sequence |ss|.
An empty sequence is denoted by |eps|, and |wp eps| is the identity function.
For the |(s;ss)| case, we have the standard definition |wp (s; ss) Q = wp s (wp ss Q)|.
%\todo{Reorganize the paragraph}
%something like: ???The cases above are rules upon a single statement; since a program is usually constituted with a sequence of statements, we use the rules 7-10, to denote assertions and specs regarding a statement sequence. |({P} Ss)| denotes...???
%SCM: I tried to refrain from categorising the previous cases as "single statements" since IF and DO are both compound statements.

The last two cases on line \ref{code:wp:seq:2} -- \ref{code:wp:seq:3} reveal that |wp| actually returns a monadic value.
For brevity we have pretended that |wp| returns a pure value in previous cases,
omitted the Haskell-ish |do| keyword,
and spelled out the keyword |return| only when it follows an effectful operation.
More about these two cases will be discussed later.
%\todo{Reorganize the paragraph}
%something like: ???|wp| is actually returning a monadic value. For brevity, we have pretended that |wp| returns a pure value in simpler cases(line1-8); when it involves effectful operations -- tellPO and tellSpec, which can be seen in the last two rules --, we explicitly spell out the keyword |return|, omitting the Haskell-ish |do| keyword.???
%SCM: We used return in line 10 too, which does not contain tellPO and tellSpec.

% this is how I see the logical flow of these 3 paragraphs: from dealing with simple cases to its true, monadic nature.

%format mu = "\mu"
\begin{figure}[t]
\numberson
\begin{spec}
wp abort     Q = False
wp skip      Q = skip
wp (x := e)  Q = Q (subst x e)
wp (IF B0 -> S0  | B1 -> S1 FI) Q  =
  (B0 || B1) && (B0 => wp S0 Q) && (B1 => wp S1 Q)
wp (DO B0 -> S0  | B1 -> S1 OD)  Q =
  mu (X -> ((B0 && B1) || Q) && (B0 => wp S0 X) && (B1 => wp S1 X))

wp eps      Q = Q                               {-"\label{code:wp:seq:0}"-}
wp (s; ss)  Q = wp s (wp ss Q)

wp ({P} Ss)    Q = struct P Ss Q; return P      {-"\label{code:wp:seq:2}"-}
wp (eSpec Ss)  Q =  Q' <- wp Ss Q               {-"\label{code:wp:seq:3}"-}
                    tellSpec [!Q', Q'!]
                    return Q'
\end{spec}
%wp (IF B0 -> S0  | B1 -> S1 FI) Q  = (B0 || B1) && (Bi => wp Si Q)
\numbersoff
\numbersreset
\caption{The weakest precondition predicate transformer.}
\label{fig:wp}
\end{figure}

\paragraph{Assertions and POs}
The conventional definition of a Hoare triple is |htriple P S Q {-"\,"-}= {-"\,"-} (P ==> wp S Q)|.
The main programs in Guabao also come in the form |htriple P S Q|.
To establish the correctness of a completed program, we could simply let the PO be the monolithic property |P ==> wp S Q|.
However, this is not helpful for program construction.
%because this would be the same as splitting program construction and proof of correctness.
%SCM: hmm.. the reason is more subtle.
We wish to produce POs that give hints to each program component that needs to be constructed.
PO generation is therefore an design issue:
we want to generate POs that are useful for program construction, and moderate in size and number.

On one thing, according to Figure~\ref{fig:wp}, a PO can be broken down along the structure of the program.
On another, given a sequence of statements, how assertions are placed reflects the intention of the programmer.
For example, given the program fragment below:
\begin{spec}
htriple2 P (S0; S1) R (S2; S3) Q  {-"~~,"-}
\end{spec}
where |S0| -- |S3| are statements containing no assertions or specs.
%SCM: The previous line cannot be omitted. Otherwise Guabao would not generate the PO below as claimed.
This could be reflecting the intention that, at the point between |S1| and |S2|,
the programmer wishes to conclude all the information about the current state, which can be used to prove the correctness of the former and the latter part of the program separately.
Therefore, Guabao should emit two POs: |R ==> wp S2 (wp S3 Q)|, and |P ==> wp S0 (wp S1 R)|.

Note that this is stronger than the traditional definition:
|wp (assert R) Q = R && Q|.
Consider the following programs (assuming |x, z : Int|):
\begin{spec}
{-"{\sf P}_0:\qquad"-}  { z > x } x := z - x; x := x / 2 { x >= 0 } {-"~~,"-}
{-"{\sf P}_1:\qquad"-}  { z > x } x := z - x { x > 0 } x := x / 2 { x >= 0 } {-"~~,"-}
{-"{\sf P}_2:\qquad"-}  { z > x } x := z - x { True } x := x / 2 { x >= 0 } {-"~~."-}
\end{spec}
Program ${\sf P}_0$ generates one PO: |z > x ==> (z-x)/2 >= 0|, while ${\sf P}_1$ generates two POs: |x > 0 ==> x/2 >= 0| and |z > x ==> z - x > 0|.
All of them can easily be discharged.
In contrast, while ${\sf P}_2$ is a valid program in the traditional setting, Guabao would generate an unprovable PO: |True ==> x/2 >= 0| (and a trivial PO: |z > x ==> True|).
We believe that this is suitable for Guabao, which is not designed to prove programs in general, but to construct programs with an intention in mind.

It is also worth noting that, while some tools for program construction demand programmers to specify intermediate conditions between every sequenced statements (that is, to construct |htriple P (S0; S1) Q| the user has to provide |R| such that |htriple2 P S0 R S1 Q| holds, see Section~\ref{sec:related-works}),
this is not so in Guabao. Instead, weakest preconditions are accumulated until we meet an assertion, where we emit a PO.

% It feels like usually, "while some tools for program construction demand..." needs a citation, I'm not sure if it's needed here.

Having assertions helps to generate more specific POs.
For example, the weakest precondition of an |IF|-statement with two branches is defined by:
\begin{spec}
 wp (IF B0 -> S0 | B1 -> S1 FI) Q =
   (B0 || B1) && (B0 ==> wp S0 Q) && (B1 ==> wp S1 Q) {-"~~."-}
\end{spec}
%Abbreviate |IF B0 -> S0 || B1 -> S1 FI| to |iif|.
Given the following program fragment:
%format iif = "\Conid{IF}"
\begin{spec}
htriple2 P S R (IF B0 -> S0 | B1 -> S1 FI) Q {-"~~,"-}
\end{spec}
our algorithm in Guabao generates the following POs:
\begin{enumerate}
\item |R && B0 ==> wp S0 Q|,
\item |R && B1 ==> wp S1 Q|,
\item |R => B0 |||| B1|, all of them being consequences of the |wp| definition above, and
\item |P ==> wp S R|, due to |htriple P S R|.
\end{enumerate}
%alone with |P ==> wp S R|.
Without the assertion |{R}| in the middle,
Guabao would have to generate one PO: |P ==> wp S (wp (IF B0 -> S0 || B1 -> S1 FI) Q)|.
The size of this expression would multiply if |S| happen to be an |IF ... FI| too.

\paragraph{PO generation}
Let us now examine the function |struct P S Q|, presented in Figure~\ref{fig:struct}, which Guabao calls to compute POs when seeing a Hoare triple |htriple P S Q|.
It is a function running in a writer monad with two methods:
|tellPO P| announces a proof obligation |P|, while |tellSpec [!P, Q!]| announces a spec with inferred precondition |P| and postcondition |Q|.

The case for |IF ... FI| is as explained before:
we output a PO: |P ==> B0 |||| B1|, while recursively compute POs for the two branches with updated precondition |P && Bi|.
The case for |DO ... OD| will be discussed later.
%More discussion about line \ref{code:struct:do:3} for {\sf TermInd} will be given later.
For other simple, non-sequence statements we fall back to |P ==> wp S Q| (line~\ref{code:struct:simp}).

\begin{figure}[t]
\numberson
\begin{spec}
struct P (IF B0 -> S0 | B1 -> S1 FI) Q =
  tellPO (P ==> B0 || B1)
  struct (P && B0) S0 Q; struct (P && B1) S1 Q

struct (P,e) (DO B0 -> S0 | B1 -> S1 OD) Q =
  tellPO (P && not (B0 || B1) ==> Q)         {-"\label{code:struct:do:0}"-}
  struct (P && B0) S0 P; struct (P && B1) S1 P
  tellPO (P && (B0 || B1) ==> b >= 0)
  termInd P e B0 S0; termInd P e B1 S1  {-"\label{code:struct:do:3}"-}

struct P s Q = tellPO (P ==> wp s Q)  {-"\label{code:struct:simp}"-} -- other simple statements

struct P eps Q     = tellPO (P ==> Q)        {-"\label{code:struct:seq:0}"-}
struct P (s;ss) Q  = Q' <- wp ss Q; struct P s Q'  {-"\label{code:struct:seq:1}"-}

struct P (ss {R} Ss) Q    = struct P ss R; struct R Ss Q     {-"\label{code:struct:seq:2}"-}
struct P (ss eSpec Ss) Q  =  P' <- sp s P; Q' <- wp Ss Q;  {-"\label{code:struct:seq:3}"-}
                             tellSpec [!P', Q'!]

termInd P e B S =  if containsSpec S then return ()
                        else  C <- newVar
                              struct (P && B && e = C) (strip S) (e < C)
\end{spec}
% struct P ({R} ss) Q     = tellPO (P => R); struct R ss Q
% struct P ([!!] ss) Q    = tellSpec [!P, wp ss Q !]
% struct' (P && B0) S0 P; struct' (P && B1) S1 P {-"\label{code:struct:do:3}"-}
\numbersoff
\numbersreset
\caption{The function |struct _ _ _|.}
\label{fig:struct}
\end{figure}

The cases for sequences of statements are trickier.
As discussed before, assertions are treated differently.
Furthermore, we need to infer pre/postconditions for specs.
Therefore we partition a sequence of statements into segments separated by assertions or specs, and process them segment-by-segment.
We call a sequence \emph{simple} if it contains no assertions or specs.
In the patterns between line~\ref{code:struct:seq:0} and \ref{code:struct:seq:3}, |ss| denotes a (possibly empty) simple sequence of statements, while |Ss| denotes any sequence.
Line \ref{code:struct:seq:0} -- \ref{code:struct:seq:1} deal with simple sequences.
For an empty sequence we simply emit |P ==> Q|.
For |(s;ss)|, we compute |wp ss Q|, and let it be the postcondition for |s|.
%\todo{a question}
% I'm not sure if the concept of general sequence is a commonsense in this community... what does it precisely mean here? From what I can see, It looks just like ss...
% SCM: I've changed it to "any sequence".

When the first simple segment |ss| is separated from the rest |Ss| by an assertion |{R}| (line \ref{code:struct:seq:2}), we recursively compute |struct P ss R| and |struct R Ss Q|.

%format ss0
%format ss1
%format ss2

Line \ref{code:struct:seq:3} deals with the case |(ss eSpec Ss)|, that is,
when a simple sequence |ss| is separated from |Ss| by a spec.
We have to compute the pre/postconditions of the spec.
Denote |wp Ss Q| by |Q'|.
Note that computation of |wp Ss Q| could in turn trigger evocations of |struct _ _ _| when there are assertions in |Ss| --- such cases would be caught by line \ref{code:wp:seq:2} of Figure~\ref{fig:wp}.
It is valid if we generate |ss [!Q', Q'!] Ss|, that is, Guabao could instruct the user to fill in a program that expects |Q'| to be established and maintain |Q'| upon completion (we would then demand the programmer to prove |htriple P s Q'|).
This is usually not very helpful, however.
Instead, we compute the \emph{strongest postcondition} of |s| with respect to |P|, and use that as the precondition of the spec.
The function |sp| that computes the strongest postcondition is defined in Figure~\ref{fig:sp}.
When specs appears consecutively (e.g. |ss0 eSpec ss1 eSpec ss2|), we will run into the last case of |wp| (line \ref{code:wp:seq:3} of Figure~\ref{fig:wp}), where we simply create |[!Q,Q!]|.~\footnote{Another choice is to create a new logical variable |V| and let the spec be |[!V,Q!]|, but since the user cannot directly edit |V|, this is not more helpful. The user may always specify the precondition of the spec by adding an assertion.}

\begin{figure}[t]
\begin{spec}
sp abort  P     = True
sp skip   P     = P
sp (x := e) P  = (exquant x' () (x = E (subst x x') && P (subst x x')))
sp (IF B0 -> S0  | B1 -> S1 FI)  P = OR (sp Si (P && Bi))
sp (DO B0 -> S0  | B1 -> S1 OD)  P =
  struct P (do B0 -> S0 | B1 -> S1 od) (P && not (B0 || B1));
  return (P && not (B0 || B1))

sp eps P      = P
sp (s; ss) P  = sp ss (sp s P)
sp (ss {Q} Ss)    P = struct P ss Q; sp Q Ss
sp (ss eSpec Ss)  P = tellSpec [!P,P!]; sp P Ss
\end{spec}
\caption{The strongest postcondition predicate transformer.}
\label{fig:sp}
\end{figure}

Finally, let us talk about the case for |DO ... OD|.
Line~\ref{code:struct:do:0} -- \ref{code:struct:do:3} in Figure~\ref{fig:struct}
respectively correspond to {\sf InvBase}, {\sf InvInd}, {\sf TermBase}, and {\sf TermInd} discussed in Section~\ref{sec:gcl}.
The last case is the most tricky.
Recall that, according to {\sf TermInd},
for each |B_i -> S_i| the programmer shall prove that |htriple (P && B_i && e = C) S_i (e < C)|.
One may want to naively make a call to |struct (P && B_i && e = C) S_i (e < C)|.
However, notice that |C| is a fresh logical variable, and that |S_i| may contain assertions, which cannot mention |C|.
As a result Guabao may end up generating unprovable POs, or produce impossible pre/postconditions for specs.

To get around the problem, the helper function |termInd| returns nothing if the loop body |S| contains specs --- we postpone generating all POs until the program is finished. If |S| contains no specs, we generate a fresh logical variable |C|, and applies |struct _ _ _| to |strip S| --- which denotes |S| with all assertions removed.

\section{Related Works}
\label{sec:related-works}

Before and during development of Guabao, we surveyed a number of projects designed for similar goals.
It is worth comparing their design choices and consequences.

CorC \cite{Schaefer:18:CorC,Runge:19:Tool} is an IDE designed to promote the correct-by-construction approach.
It comes with a hybrid graphical and textual interface.
In its graphical interface, the user starts with a box labelled with pre/postconditions, representing a spec |[!P, Q!]|.
There is a menu from which the user may choose what the spec is to be refined to.
To refine the spec to |[!P, R!]; [!R, Q!]|, for example, the user choose "Composition Statement" from the menu, which generates a new node under the spec.
The user is then required to provide |R| in the new node, \emph{before} two subtrees representing |[!P, R!]| and |[!R, Q!]| can be created and further refined.
CorC also provides a textual interface, which works by the same principle:
programs are created by refining specs,
and to refine a spec, the user must provide pre/postconditions.
While we felt that it was not the ideal style of interaction we would prefer,
the experience with CorC motivated the creation of Guabao.

Dafny \cite{Leino:14:Dafny} is a programming language and environment for program development and verification.
As the user types in a program, Dafny verifies it by computing sufficient verification conditions and delegates them to an SMT solver, signals errors, and displays counter examples when a program does not meet the specification.
The language provides a wide spectrum of features including
inductive datatypes, classes and inheritance, recursive functions, mutable data structures.
Verified program can be compiled to Java, C\#, etc.
Dafny is built around the model that the user programs and the system proves,
while we wish the user to be more actively engaged in the proving aspect, and let proving guide programming.
Still, in many aspects Dafny is a matured, ideal environment that meets our needs and offers much more --- we might not have developed Guabao had we known about Dafny earlier.
We wish that Guabao will eventually grow into a system that is as complete as Dafny.

CAPS (Calculational Assistant for Programming from Specifications) \cite{Chaudhari:14:Automated,Chaudhari:15:Building} is a system for derivation of imperative programs.
Both CAPS and Guabao use a variation of Guarded Command Language and mathematical notations heavily influenced by Kaldewaij~\cite{Kaldewaij:90:Programming}.
In contrast to the free-form text editing of Guabao, CAPS chose a tactic based approach.
Programs cannot be edited directly and must be manipulated through tactics.
For example, ``IfIntro'' introduces an |IF| statement,
``WhileStrInv'' strengthens the invariant of a loop, etc.
Tactics are also used to manipulate formulae, and these formulae can be fed back to tactics manipulating programs.
Crucial proofs can be delegated to SMT solvers.
Due to the tactic-based approach, programs in CAPS are represented by and displayed as diagrams.
One of the advantages is that CAPS maintains the full history of program development.
The user can easily roll back to a previous stage and start a new experimental branch.

\section{Conclusions and Future Work}
\label{sec:conclude}

We have presented a preliminary implementation of Guabao, an integrated environment for imperative program derivation.
Its noticeable features, when compared with contemporary tools serving similar purposes, include: a free-form editing interface which encourages programs and proofs to be developed together; pre/postconditions of specs are inferred; assertions trigger generation of localised proof obligations.

We have used Guabao in an undergraduate course on imperative programming.
Most of the feedback from students were suggestions about elements of the interface.
For example, previous versions of Guabao labelled code with POs using wavy underline, which felt like errors to some students.
Some students find it cumbersome using the UTF-8 input method.
These suggestions helped to improve Guabao.
It is still too preliminary, however, to draw conclusion on how much Guabao helps students in learning program derivation.
We hope to conduct a more through survey when Guabao grows into a more matured system.

A lot remains to be done.
To begin with, Guabao needs to be equipped with a sufficient library of standard functions and subroutines.
We also plan to extend Guabao with a number of features including procedure calls and the ability to manipulate data structures with pointers.
To describe properties of such structure, the language in the assertions of Guabao needs to be extended to a more complete functional language.
Finally, to verify the proofs written by users, we need a formal representation of equational proofs.
For this purpose, the aforementioned functional language could be a language with dependent type, in which proofs can be represented by Curry-Howard correspondence.
Or we can delegate the job to an existing theorem prover and use its language.
It remains to see what is the most suitable.

\subsubsection{Acknowledgements}
We would like to thank the members of PLFM group in IIS, Academia Sinica,
in particular Bow-Yaw Wang, for his support of this project,
and to members of IFIP Working Group 2.1, in particular Carroll Morgan,
for his insightful opinions and valuable discussions.

%% Bibliography
\bibliographystyle{splncs04}
\bibliography{guabao}
%\input{LongParens.bbl}

\end{document}
