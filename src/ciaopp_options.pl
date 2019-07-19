:- package(ciaopp_options).
% Global definitions for CiaoPP modules

% (comment/uncomment to change the defaults)

%% Included CiaoPP features (select one)
:- compilation_fact(with_fullpp).   % full [default]
%:- compilation_fact(with_minipp).  % reduced footprint

%% Module header declarations for output 
:- compilation_fact(preserve_mod_headers). % try to preserve from source [default]
% (empty)                                  % from p_unit exported

:- include(ciaopp(ciaopp_config_auto)).
