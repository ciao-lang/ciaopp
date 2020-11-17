:- use_package(assertions).

:- doc(filetype, part).

:- doc(title, "Available type domains and widenings").

:- doc(module, "

@section{Available widenings}
All widenings are briefly described in the eterms domain paper @cite{eterms-sas02}

@begin{verbatim}
+-----------------+-----------+---------+--------+-------------+------+---------------------+
|Widening         |Implemented|Domain   |Typeslib|Using 'names'|Tested|Working              |
+-----------------+-----------+---------+--------+-------------+------+---------------------+
|Type Jungle      | yes       |evalterms| yes    |yes (why?)   | no   |not connected to plai|
|Shortening       | yes       |termsd   | yes    |no           |barely| apparently          |
|Topological Clash| yes       |ptypes   | yes    |no           |barely| no                  |
|Structural       | yes       |eterms   | yes    |yes          | yes  |yes (slow)           |
|Depth            | no        |         |        |             |      |                     |
|Functor          | no        |         |        |             |      |                     |
+-----------------+-----------+---------+--------+-------------+------+---------------------+
@end{verbatim}

Restricted shortening is also implemented according to comments in termsd.

@section{Other type domains}

@begin{verbatim}
+---------+----------------+--------+-----------------+------+-----------------+
| Domain  |widening needed?|Typeslib|Using 'names'    |Tested|Working          |
+---------+----------------+--------+-----------------+------+-----------------+
| svterms |yes (structural)| yes    | yes (structural)|barely|apparently (slow)|
| deftypes|no              | yes    | no              |barely| apparently      |
| depthk  |no              | no     | no              |barely| ?               |
+---------+----------------+--------+-----------------+------+-----------------+
@end{verbatim}

@section{Some experiments}
Some very simple experiments FixFail means that analyzing with plai the message
\"Something has failed\" appeared.

Benchmarks are located in @tt{ciaopp/tests/benchs/widening/} list_of_lists and
sorted were used because they are used as examples in the eterms paper.
@code{minimal_lists} and @code{minimal_functors} were designed to capture the
complexity problem that currently eterms has.

@begin{verbatim}
+-----------------+-------------+-------+-------------+----------------+
|Widening         |list_of_lists|sorted |minimal_lists|minimal_functors|
+-----------------+-------------+-------+-------------+----------------+
|Shortening       | 2.532       | 30.195| 26.668      | 9.28           |
|Topological Clash| FixFail     |FixFail| FixFail     | FixFail        |
|Structural       | 2.388       | 2.855 | 23161.302   | 9.822          |
|svterms          | 3.183       | 3.443 | 37948.465   | 8.553          |
|deftypes         | 1.647       | 2.348 | 2.603       | 8.803          |
|depthk           | 8.527       | 5.725 | 4.879       | 7.11           |
+-----------------+-------------+-------+-------------+----------------+
@end{verbatim}

For structural widening, e.g. using domain eterms or svterms, analyzing
@code{minimal_lists} creates 1500 types.
 ").
