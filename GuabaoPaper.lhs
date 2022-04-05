% build using
%    lhs2TeX GuabaoPaper.lhs | pdflatex --jobname=GuabaoPaper

\documentclass[runningheads]{llncs}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include GCL.fmt

\include{macros}

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
Thing-Han Lim\inst{1}}
%
\authorrunning{S-C. Mu  et al.}

\institute{
Institute of Information Science, %\\
Academia Sinica, Taiwan}


\maketitle              % typeset the header of the contribution
%
\begin{abstract}
The abstract should briefly summarize the contents of the paper in
150--250 words.

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
Backhouse:03:Program,Backhouse:11:Algorithmic} collectively developed a methodology of program development from specification: how to construct a loop invariant from a desired postcondition; how to construct the loop body from its last step; how to ensure termination, etc.
This methodology was applied to derive algorithms
solving individual small problems
(e.g~\cite{Rem:89:Small,Rem:90:Small}) as well as families of problems (e.g~\cite{Zantema:92:Longest}).
Meanwhile, derivation of functional programs, a closely related topic, has also been developing (e.g~\cite{Bird:10:Pearls}).
Within the advocating community it is at least wished that the concept of program derivation should be taught as part of the fundamental training for programmers and computing science majors.
% These days, program derivation is more practiced in the functional programming community. Derivation of imperative programs, however, is also a field with rich possibilities and potentials.

Since 2011, the first author has been teaching an undergraduate level Programming Languages course, in which imperative program derivation is covered.
From the experiences accumulated, we felt that such a course would benefit from having a supporting tool.
Therefore we created Guabao.
The aim is to develop a programming environment having the following features:
\begin{enumerate}
\item It encourages {\bf developing proofs and programs together}.
While the user may certainly write up all the code in Guabao and verify it afterwards, the interface shall allow the user to interleave proving and coding, and let the two modes aid each other.
\item It encourages {\bf backward-reasoning}.
Since it is easier to construct the weakest precondition of an assignment from its postcondition then the other way round,
to construct a block of statements, many derivation techniques start with thinking about what the \emph{last assignment} could be.
The interface of Guabao should make such construction easy and natural.
\item It allows {\bf free-form text editing}, as opposed to treating programs as diagrams as some program construction tools do, since we believe it what most programmers would prefer.
\end{enumerate}
In Section~\ref{sec:programming-example} we will see an example demonstrating all these features.
It might also help to clarify what Guabao is not.
\begin{enumerate}
\item Gaubao is not (merely) an implementation of Guarded Command Language (GCL).
Dijkstra~\cite{Dijkstra:98:Cruelty} wrote that he would
design a programming language for teaching (which we believe would be GCL) and ``see to it that [it] has not been implemented on campus so that students are protected from the temptation to test their programs.''
Gaubao is not an implementation of GCL in which one can write a program and test it, but an environment where a program and its proof can be designed together.
One cannot yet execute the program --- although it is not difficult to implement an interepreter and allow a program to run once all proofs are done.
\item \todo{Guabao does not check your proof.}
\end{enumerate}

Currently, Guabao is implemented as an extension of the editor Visual Code Studio,
which can be installed by searching for the extension "Guabao" in the editor, or through its Extensions Marketplace~\footnote{\url{https://marketplace.visualstudio.com/items?itemName=scmlab.guabao}}.
A simple one-click installation downloads the frontend and the pre-compiled backend.
%The readers are welcomed to give it a try!
The backend of Guabao is implemented using Haskell~\cite{PeytonJones:03:Haskell}, while the frontend is implemented using Reason~\cite{Walke:16:Reason} and compiled to Javascript to run as a VS Code extension.
Regarding its name,
GUA in Guabao comes from GUArded command language.
Guabao (\cjk{刈包}) is a street food popular in places including Taiwan, where Guabao the software was designed.

% \section{Motivation}
% \label{sec:motivation}
%
% Derivation of functional programs is relatively linear. We start from a specification, transform it to the next, until we have a program whose performance we are happy about.
% Shown below is an outline derivation of the classical ``maximum segment sum'' (MSS) problem --- that is, given a list of numbers, compute the largest sum of a consecutive segment:
% \begin{spec}
%    maximum . map sum . concat . map inits . tails  -- problem specification
% =    {- since |map f . concat = concat . map (map f)| -}
%    maximum . concat . map (map sum) . map inits . tails
% =    {- other properties -}
%    ...
% =    {- more properties -}
%    maximum . scanr oplus 0 {-"~~."-}               -- a faster program
% \end{spec}
% The problem specification in the first line is a functional program that exhaustively generates all segments, computes the sums for each of them, and picks the maximum.
% The point here is not the technical details but the style.
% The derivation is a consecutive, long chunk of calculation proof.
% Properties needed (such as |map f . concat = concat . map (map f)|) can be proved as a separate lemma, and when we do so, its relationship to the main proof is clear.
% If the derivation does not work, we may realise (by inspecting what is missing in the derivation) that we need to start from a more general specification.
% We then construct the new specification, and start over again.
% All these proceed in a way similar to doing mathematical proofs on a piece of paper, from top of the page to the bottom.
% In fact, such derivations was indeed often carried out on paper.
%
% Not having proper tools, derivations of imperative programs were also mostly carried out on paper. However, the experience is less linear and much more messy -- it is more like keeping writing and erasing symbols on a white board.
% Consider also the MSS problem, where the input is an array |A| of |N| integers.
% One might expect that the problem will be solved using a loop.
% In the \emph{Guarded Command Language}~\cite{Dijkstra:75:Guarded} a while-loop (with a single body) is denoted by:
% \begin{spec}
% htriple (P, bnd: e) (DO B -> S OD) Q
% \end{spec}
% where |P| is the loop invariant, |e| the \emph{bound} (a value that strictly decreases after each iteration of the loop), and |Q| the postcondition.
% When the \emph{guards} |B|, the command |S| is executed and the loop gets iterated again; otherwise the loop exits.
%
% Once we introduce a loop, however, we have also gave ourselves \emph{four} proof obligations:
% \begin{enumerate}
% \item |P && not B ==> Q|,
% \item |htriple (P && B) S P|,
% \item |P && B ==> e >= 0|,
% \item |htriple (P && B && e = C) S (e < C)|.
% \end{enumerate}
% The first two properties guarantee that the loop is partially correct: that is, if the loop terminates at all, it terminates in a state satisfying |Q|. The last two properties establishes that the loop actually terminates. The four properties together guarantee total correctness.
% Often, one or two of the properties are rather trivial.
% Still, they need to be proved.
%
% For the MSS problem we may choose |Q <=> (s = mss N)|, where
% |mss n = maxquant (p q) (0 <= p <= q <= n) (sum p q)|, the maximum sum of all segments in |arrayCO A 0 n|, and |sum p q| computes the sum of |arrayCO A p q|.
% A common strategy is to establish the postcondition using a loop in which we keep increment a variable |n| until it reaches |N|. Therefore we come up with the following program skeleton:
% \begin{spec}
% s,n := 0,0
% (assert (s = mss n, bnd: N-n))
% DO n /= N ->  [:  s = mss n && n /= N,
%                   s = mss (n + 1) :]
%               n := n + 1
% OD
% (assert (s = mss N))  {-"~~,"-}
% \end{spec}
% where
% |[: pre, post :]| denotes a \emph{spec} --- a piece of program yet-to-be-finished that is supposed to establish postcondition |post| given precondition |pre|.
%
% % Transition from the previous program to this one is like tweaking expressions on a white board.
% To further refine the specification, one may try to find a way to efficiently update |s|. It will turn out that this can only be done by introducing an auxiliary variable:
% \begin{spec}
% s,n := 0,0
% (assert (s = mss n && t = msf n, bnd: N-n))
% DO n /= N ->  [:  s = mss n && t = msf n && n /= N,
%                   s = mss (n + 1) && t = msp (n +1) :]
%               n := n + 1
% OD
% (assert (s = mss N))  {-"~~,"-}
% \end{spec}
% where |msf n| denotes the maximum sum of \emph{suffixes} of |arrayCO A 0 n|.
%
% Once we introduce |t|, the four proof obligations are also updated accordingly and need to be proved again.
%
% Finally, to prove termination, one may realise that we need additional constraints on |n|: |0 <= n <= N|. This again changes our proof obligations.
%
% Development of an imperative program is like scribbling on a whiteboard, where the programmer may make changes here and there. The required proof obligations updates accordingly. The challenge of the programmer is to come up with the program, while making sure that all the proofs to be done are possible. When doing the proof, the programmer may realise that the program may need further generalisation to make the proof possible at all (it is in the spirit of Dijkstra’s methodology, that proofs and programs should be developed hand-in-hand).
%
% It is certainly error-prone keeping track of all these proofs. When teaching, it is hard to give students a systematic idea what proofs are involved. A tool thats keeps track of all the proof obligations would be a much clearer and systematic presentation of the technique. Outside the classroom, such a tool would be helpful for experimenting with different strategies for developing algorithms. The developing environment could also employ external tools, such as a theorem prover or an SMT solver, to discharge the proof obligations.
%


\section{The Guarded Command Language}

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
which we will briefly review in this section for completeness.
A condensed presentation of its abstract syntax is given in Figure~\ref{fig:gcl-syntax}.
A program consists of a section of declarations followed by a section of statements.
Constant and variable declarations respectively start with keywords |VAR| and |CON|.
They can be accompanied by an optional assertion stating properties we assume about the declared entities.

An assertion is a Boolean-valued expression in curly brackets.
By the convention of the program derivation community, a \emph{Hoare triple} |htriple P S Q| denotes total correctness: that is, the program |S|, when executed in a state satisfying |P|, \emph{terminates} in a state satisfying |Q|.
We prefer it than the partial correctness interpretation (that is, |S| establishes |Q| \emph{if} it terminates) because, as we will see in Section~\ref{sec:programming-example}, that the program must terminate provides useful hints how it can be written.
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
A group of guarded commands surrounded by |IF ... FI| denotes conditional branches.
For example, |IF B0 -> S0 || B1 -> S1 FI| has two branches, where |Si| is executed if |Bi| holds (|i `elem` {0,1}|).
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
where |P| is the loop invariant, |e| the bound , and |Q| the postcondition.

Once we introduce such a loop, however, we have also given ourselves \emph{four} proof obligations:
\begin{spec}
{-"\mbox{1. \sf InvBase}:\qquad"-}   P && not (B0 || B1) ==> Q {-"~~,"-}
{-"\mbox{2. \sf InvInd}:\qquad"-}    htriple (P && Bi) Si P {-"\mbox{,~~for~}"-} i `elem` {0,1} {-"~~,"-}
{-"\mbox{3. \sf TermBase}:\qquad"-}  P && (B0 || B1) ==> e >= 0 {-"~~,"-}
{-"\mbox{4. \sf TermInd}:\qquad"-}   htriple (P && Bi && e = C) Si (e < C) {-"\mbox{,~~for~}"-} i `elem` {0,1} {-"~~."-}
\end{spec}
% \begin{enumerate}
% \item[({\sf InvBase})] |P && not (B0 |||| B1) ==> Q|,
% \item[({\sf InvInd})] |htriple (P && Bi) Si P| for |i `elem` {0,1}|,
% \item[({\sf TermBase})] |P && (B0 |||| B1) ==> e >= 0|,
% \item[({\sf TermInd})] |htriple (P && Bi && e = C) Si (e < C)| for |i `elem` {0,1}|.
% \end{enumerate}
Properties {\sf InvBase} and {\sf InvInd} guarantee that the loop is partially correct: that is, if the loop terminates at all, it terminates in a state satisfying |Q|.
{\sf TermBase} and {\sf TermInd} establish that the loop does terminate.
The four properties together guarantee total correctness.

One can imagine that, as the size of program grows, the number of proof obligations may soon grows out of hand.
\footnote{With proper use of assertions, the size of proof obligations can be limited to be linear in the size of the program \cite{Dijkstra:69:Understanding}. Still, that is a lot of properties to prove.}
It happens often that some of the properties are rather routine, but they still need to be proved.
It would be nice to have an environment that keeps tracks of these proof obligations.
Even better, the environment shall encourage the idea that programs can be designed around having to discharge these proof obligations.
Therefore the proofs are no longer additional burden, but useful guides during program development.

\section{Programming in Guabao}
\label{sec:programming-example}

In this section we demonstrate the user experience of program development in Guabao.
As our worked example, consider the problem: given natural numbers |A| and |B|,
compute |A * B| using only addition, subtraction, predicates |even| and |odd|, and multiplication and division by |2|.
This is a classical exercise, and was once a useful one for early microcomputers, which did not have an atomic instruction for general multiplication (multiplication by |2| involves only bit-shifting and is much cheaper).

Specification of the problem is shown below.
We declare two constants |A| and |B|, about them all we know is that they are both non-negative (as asserted in |assert (A >= 0 && B >= 0)|).
Functions |even| and |odd|, which we will use later,
are declared as constants.
Also declared is a variables |r| having type |Int|.
The goal of the program is to store the value of |A * B| in variable |r|, as stated in the postcondition |assert (r = A * B)|.
The question mark indicates code yet to be written.
\begin{spec}
CON A, B : Int (assert (A >= 0 && B >= 0))
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
Once the code is pasted into Guabao, we will see:\\
\sshotimg{sshot00}
Guabao automatically expands the question mark |?| to a \emph{spec} — a hole in the program to be filled in, denoted by |[! ... !]|.
The idea of a spec is inspired by Morgan~\cite{Morgan:90:Programming}, with a slight difference: in Morgan~\cite{Morgan:90:Programming} one starts program construction from a spec with given pre and postconditions, while in Guabao the pre and postconditions are inferred.
The interface shows, on line 5 and 7, that code to be filled in shall bring the state of the system from precondition |True| to postcondition |r = A * B|. Properties of global constants (namely |A >= 0 && B >= 0|) are universally true and implicitly conjuncted with all assertions. They are displayed separately in a ``Property'' section in the right pane.

\paragraph{Introducing a Loop}
For such a non-trival task we expects that a loop is needed,
so we try to fill in the spec:
\\\sshotimg{sshot01}\\
To construct a loop we must think about its invariant and bound.
Various techniques were developed to construct candidates of loop invariants from the postcondition.
We cannot properly cover the techniques in this paper but, for interested readers, we recommend Kaldewaij~\cite{Kaldewaij:90:Programming}.
For this problem, we use one of the standard tricks:
choose |a * b + r = A * B| as the loop invariant (line 7), which can be established by initialisation |a, b, r := A, B, 0| (line 6).
By letting the guard be |b /= 0| (line 8), the proof obligation {\sf InvBase} instantiates to |a * b + r = A * B && b = 0 ==> r = A * B|, which is trivial to prove.
Now that the loop terminates when |b = 0|, a strategy would be to keep decreasing |b| in the loop body until it reaches |0|,
therefore we let |b| be the bound (line 7).
The loop body is left as a question mark.

When the cursor is in the spec, press {\tt ctrl-c-r} to fill in the spec.
In the screenshot in the top of Figure~\ref{fig:sshot23}, the code typed into the hole becomes part of the program,
while the question mark becomes a new hole.
\footnote{This style of interaction (including the hot-key combination) is inspired by Agda.}
The pre and postconditions are calculated from {\sf InvInd}.
%\\\sshotimg{sshot02}\\

\begin{figure}
\sshotimg{sshot02}\\
\sshotimg{sshot03}
\caption{Top: after introducing a loop. The proof obligations come respectively from {\sf InvBase} and {\sf TermBase}. Pre and postconditions of the spec are from {\sf InvInd}. Bottom: clicking on the hash introduces a proof block.}
\label{fig:sshot23}
\end{figure}

\paragraph{The Interface}
Let us get a closer look at the interface of Guabao.
%Now it is a good time to inspect the interface of Guabao.
In the program in the left pane,
blue shade in the code indicates ``there are proof obligations incurred here.''
Program locations associated with more proof obligations get a thicker shade.
The right pane contains information including
\begin{itemize}
\item inferred proof obligations,
\item pre and postconditions of specs,
\item global properties, etc.
\end{itemize}
Since the number of proof obligations can be large, in the right pane we display those on the path of the current location of the cursor.
In Figure~\ref{fig:sshot23}, the cursor is at line 7, beginning of the loop.
Proof obligations in the right pane include:
\begin{spec}
a * b + r = A * B  && not  (b /= 0)   ==>  r = A * B  {-"~~, \mbox{which is {\sf InvBase}, and}"-}
a * b + r = A * B  &&      b /= 0     ==>  b >= 0     {-"~~, \mbox{which is {\sf TermBase}}."-}
\end{spec}
%The first one is aforementioned {\sf InvBase}, while the second is {\sf TermBase}.

Each proof obligation comes with a hash key. Clicking on the hash key for the first proof obligation, for example, results in the screenshot in the bottom of Figure~\ref{fig:sshot23}.
%\\\sshotimg{sshot03}\\
A new comment block having the hash key is added to the bottom of the code, in which the programmer can write up a proof of the corresponding property.
A program is proven correct if all proof obligations are proved.
Hash key of a proof obligation with a proof block is displayed in blue (see the top-right corner).
Currently the system makes no attempt to check these proofs, however.
They are just comments for the user.

Once we start doing the proofs, it immediately turns out that we cannot prove {\sf TermBase} --- the premise does not guarantee |b >= 0|! We thus realise that we need a stronger invariant. The new invariant would be
\begin{spec}
 a * b + r = A * B  &&  b >= 0 {-"~~."-}
\end{spec}
After the user updates the invariant, the proof obligations and the specs are updated accordingly.

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

\begin{figure}[h]
\sshotimg{sshot04}\\
\sshotimg{sshot05}
\caption{Top: guessing that the last statement could be |b := b / 2|.
Bottom: trying to fill in |b := b * 2| in the loop body. It will turn out that we cannot prove {\sf TermInd}.}
\label{fig:sshot45}
\end{figure}

One possibility is filling in |b := b * 2|.
That, however, results in the bottom of Figure~\ref{fig:sshot45}, where
Proof obligation {\sf TermInd}, shown in the right pane, demands us to prove that
%format bnd_0 = "{?bnd_{51}}"
\begin{spec}
.... b = bnd_0 ... ==> (b * 2) / 2 < bnd_0 {-"~~,"-}
\end{spec}
where |bnd_0| is a system-generated logical variable.
This property cannot be proved, and
we learn that |b := b * 2; b := b / 2| is a bad idea as the loop body --- the bound |b| does not decrease.

Another possible choice is |a := a * 2|.
For that we have to prove an proof obligation induced from {\sf InvInd}, which simplifies to
\begin{spec}
(a * b) + r = A * B .... {-"~~"-}  ==> {-"~~"-} ((a * 2) * (b / 2)) + r = A * B ....
\end{spec}
which, under integral division, can be true \emph{provided that |b| is an even number}.
This is a hint that we shall wrap |a := a * 2; b := b / 2| in a guard |even b|, to ensure that |b| is even, and put it in an |IF| construct.
The current code is:
\begin{spec}
DO b /= 0 ->
  IF even b ->  a := a * 2
                b := b / 2
  FI
OD
\end{spec}

\paragraph{Totalising |IF|}
We are not done yet. Among all the proof obligations we will be asked to prove that |IF| is total --- every possible case is covered.
Therefore we need to think about what to do in the |odd b| case. For this case we might decrease |b| by |b := b - 1|. By a similar process we can construct what to do with |a| and |r| in this case to maintain the invariant. A possible final program would be
(omitting the declarations):
\begin{spec}
a, b, r := A, B, 0
(assert (a * b + r = A * B && b >= 0, bnd: b))
DO b /= 0 ->  IF  even b  ->  a := a * 2
                              b := b / 2
              |   odd b   ->  r := a + r
                              b := b - 1
              FI
OD
(assert (r = A * B))
\end{spec}
which computes |A * B| using $O(\log B)$ atomic arithmetic operations.

But that is not the only possible program. One might also decide to do nothing in the |odd b| case and always decrease |b| regardless of its parity, resulting in

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
(assert (r = A * B))
\end{spec}
The program is correct as long as one can prove all the proof obligations.

\paragraph{Summary}
Let us recapitulate the interaction between a program and its proof in this example.
Certainly, the program determines what ought to be proved --- introducing a statement also introduces corresponding proof obligations.
Meanwhile, these proof obligations also gave hints on how to proceed with program construction.
One may design the program --- for example, choosing the loop guard or choosing a method to decrease the bound --- such that some obligations are trivial to prove.
Pre and postconditions of a spec, inferred from future proof obligations, shows what a piece of code is supposed to do.
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

\cite{Runge:19:Tool}
\cite{Leino:14:Dafny}
\cite{Chaudhari:15:Building}

\section{Behind the Scenes}

\begin{spec}
wp abort =
\end{spec}

\subsubsection{Acknowledgements} Please place your acknowledgments at
the end of the paper, preceded by an unnumbered run-in heading (i.e.
3rd-level heading).


%% Bibliography
\bibliographystyle{splncs04}
\bibliography{guabao}
%\input{LongParens.bbl}

\end{document}
