import LambdaCantor.Certificates.IntegerLogSources00
import LambdaCantor.Certificates.IntegerLogSources01
import LambdaCantor.Certificates.IntegerLogSources02
import LambdaCantor.Certificates.IntegerLogSources03
import LambdaCantor.Certificates.IntegerLogSources04
import LambdaCantor.Certificates.IntegerLogSources05
import LambdaCantor.Certificates.IntegerLogSources06
import LambdaCantor.Certificates.IntegerLogSources07
import LambdaCantor.Certificates.IntegerLogSources08
import LambdaCantor.Certificates.IntegerLogSources09
import LambdaCantor.Certificates.IntegerLogSources10
import LambdaCantor.Certificates.IntegerLogSources11
import LambdaCantor.Certificates.IntegerLogSources12
import LambdaCantor.Certificates.IntegerLogSources13
import LambdaCantor.Certificates.IntegerLogSources14
import LambdaCantor.Certificates.IntegerLogSources15
import LambdaCantor.Certificates.IntegerLogSources16
import LambdaCantor.Certificates.IntegerLogSources17
import Mathlib.Tactic.IntervalCases

namespace LambdaCantor.Integer

/-- All nonexceptional exponents from 4 through 300 have a source satisfying
the exact printed logarithmic predicate, with repaired prefixes where necessary. -/
theorem finite_refined_log_sources (n : ℕ) (lower : 4 ≤ n) (upper : n ≤ 300)
    (exceptional : n ∉ ([9,10,23,25,28,31,32,78,82] : List ℕ)) :
    ∃ source : LogSourceData, source.Valid n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at exceptional
  interval_cases n
  · exact refined_log_source_4
  · exact refined_log_source_5
  · exact refined_log_source_6
  · exact refined_log_source_7
  · exact refined_log_source_8
  · omega
  · omega
  · exact refined_log_source_11
  · exact refined_log_source_12
  · exact refined_log_source_13
  · exact refined_log_source_14
  · exact refined_log_source_15
  · exact refined_log_source_16
  · exact refined_log_source_17
  · exact refined_log_source_18
  · exact refined_log_source_19
  · exact refined_log_source_20
  · exact refined_log_source_21
  · exact refined_log_source_22
  · omega
  · exact refined_log_source_24
  · omega
  · exact refined_log_source_26
  · exact refined_log_source_27
  · omega
  · exact refined_log_source_29
  · exact refined_log_source_30
  · omega
  · omega
  · exact refined_log_source_33
  · exact refined_log_source_34
  · exact refined_log_source_35
  · exact refined_log_source_36
  · exact refined_log_source_37
  · exact refined_log_source_38
  · exact refined_log_source_39
  · exact refined_log_source_40
  · exact refined_log_source_41
  · exact refined_log_source_42
  · exact refined_log_source_43
  · exact refined_log_source_44
  · exact refined_log_source_45
  · exact refined_log_source_46
  · exact refined_log_source_47
  · exact refined_log_source_48
  · exact refined_log_source_49
  · exact refined_log_source_50
  · exact refined_log_source_51
  · exact refined_log_source_52
  · exact refined_log_source_53
  · exact refined_log_source_54
  · exact refined_log_source_55
  · exact refined_log_source_56
  · exact refined_log_source_57
  · exact refined_log_source_58
  · exact refined_log_source_59
  · exact refined_log_source_60
  · exact refined_log_source_61
  · exact refined_log_source_62
  · exact refined_log_source_63
  · exact refined_log_source_64
  · exact refined_log_source_65
  · exact refined_log_source_66
  · exact refined_log_source_67
  · exact refined_log_source_68
  · exact refined_log_source_69
  · exact refined_log_source_70
  · exact refined_log_source_71
  · exact refined_log_source_72
  · exact refined_log_source_73
  · exact refined_log_source_74
  · exact refined_log_source_75
  · exact refined_log_source_76
  · exact refined_log_source_77
  · omega
  · exact refined_log_source_79
  · exact refined_log_source_80
  · exact refined_log_source_81
  · omega
  · exact refined_log_source_83
  · exact refined_log_source_84
  · exact refined_log_source_85
  · exact refined_log_source_86
  · exact refined_log_source_87
  · exact refined_log_source_88
  · exact refined_log_source_89
  · exact refined_log_source_90
  · exact refined_log_source_91
  · exact refined_log_source_92
  · exact refined_log_source_93
  · exact refined_log_source_94
  · exact refined_log_source_95
  · exact refined_log_source_96
  · exact refined_log_source_97
  · exact refined_log_source_98
  · exact refined_log_source_99
  · exact refined_log_source_100
  · exact refined_log_source_101
  · exact refined_log_source_102
  · exact refined_log_source_103
  · exact refined_log_source_104
  · exact refined_log_source_105
  · exact refined_log_source_106
  · exact refined_log_source_107
  · exact refined_log_source_108
  · exact refined_log_source_109
  · exact refined_log_source_110
  · exact refined_log_source_111
  · exact refined_log_source_112
  · exact refined_log_source_113
  · exact refined_log_source_114
  · exact refined_log_source_115
  · exact refined_log_source_116
  · exact refined_log_source_117
  · exact refined_log_source_118
  · exact refined_log_source_119
  · exact refined_log_source_120
  · exact refined_log_source_121
  · exact refined_log_source_122
  · exact refined_log_source_123
  · exact refined_log_source_124
  · exact refined_log_source_125
  · exact refined_log_source_126
  · exact refined_log_source_127
  · exact refined_log_source_128
  · exact refined_log_source_129
  · exact refined_log_source_130
  · exact refined_log_source_131
  · exact refined_log_source_132
  · exact refined_log_source_133
  · exact refined_log_source_134
  · exact refined_log_source_135
  · exact refined_log_source_136
  · exact refined_log_source_137
  · exact refined_log_source_138
  · exact refined_log_source_139
  · exact refined_log_source_140
  · exact refined_log_source_141
  · exact refined_log_source_142
  · exact refined_log_source_143
  · exact refined_log_source_144
  · exact refined_log_source_145
  · exact refined_log_source_146
  · exact refined_log_source_147
  · exact refined_log_source_148
  · exact refined_log_source_149
  · exact refined_log_source_150
  · exact refined_log_source_151
  · exact refined_log_source_152
  · exact refined_log_source_153
  · exact refined_log_source_154
  · exact refined_log_source_155
  · exact refined_log_source_156
  · exact refined_log_source_157
  · exact refined_log_source_158
  · exact refined_log_source_159
  · exact refined_log_source_160
  · exact refined_log_source_161
  · exact refined_log_source_162
  · exact refined_log_source_163
  · exact refined_log_source_164
  · exact refined_log_source_165
  · exact refined_log_source_166
  · exact refined_log_source_167
  · exact refined_log_source_168
  · exact refined_log_source_169
  · exact refined_log_source_170
  · exact refined_log_source_171
  · exact refined_log_source_172
  · exact refined_log_source_173
  · exact refined_log_source_174
  · exact refined_log_source_175
  · exact refined_log_source_176
  · exact refined_log_source_177
  · exact refined_log_source_178
  · exact refined_log_source_179
  · exact refined_log_source_180
  · exact refined_log_source_181
  · exact refined_log_source_182
  · exact refined_log_source_183
  · exact refined_log_source_184
  · exact refined_log_source_185
  · exact refined_log_source_186
  · exact refined_log_source_187
  · exact refined_log_source_188
  · exact refined_log_source_189
  · exact refined_log_source_190
  · exact refined_log_source_191
  · exact refined_log_source_192
  · exact refined_log_source_193
  · exact refined_log_source_194
  · exact refined_log_source_195
  · exact refined_log_source_196
  · exact refined_log_source_197
  · exact refined_log_source_198
  · exact refined_log_source_199
  · exact refined_log_source_200
  · exact refined_log_source_201
  · exact refined_log_source_202
  · exact refined_log_source_203
  · exact refined_log_source_204
  · exact refined_log_source_205
  · exact refined_log_source_206
  · exact refined_log_source_207
  · exact refined_log_source_208
  · exact refined_log_source_209
  · exact refined_log_source_210
  · exact refined_log_source_211
  · exact refined_log_source_212
  · exact refined_log_source_213
  · exact refined_log_source_214
  · exact refined_log_source_215
  · exact refined_log_source_216
  · exact refined_log_source_217
  · exact refined_log_source_218
  · exact refined_log_source_219
  · exact refined_log_source_220
  · exact refined_log_source_221
  · exact refined_log_source_222
  · exact refined_log_source_223
  · exact refined_log_source_224
  · exact refined_log_source_225
  · exact refined_log_source_226
  · exact refined_log_source_227
  · exact refined_log_source_228
  · exact refined_log_source_229
  · exact refined_log_source_230
  · exact refined_log_source_231
  · exact refined_log_source_232
  · exact refined_log_source_233
  · exact refined_log_source_234
  · exact refined_log_source_235
  · exact refined_log_source_236
  · exact refined_log_source_237
  · exact refined_log_source_238
  · exact refined_log_source_239
  · exact refined_log_source_240
  · exact refined_log_source_241
  · exact refined_log_source_242
  · exact refined_log_source_243
  · exact refined_log_source_244
  · exact refined_log_source_245
  · exact refined_log_source_246
  · exact refined_log_source_247
  · exact refined_log_source_248
  · exact refined_log_source_249
  · exact refined_log_source_250
  · exact refined_log_source_251
  · exact refined_log_source_252
  · exact refined_log_source_253
  · exact refined_log_source_254
  · exact refined_log_source_255
  · exact refined_log_source_256
  · exact refined_log_source_257
  · exact refined_log_source_258
  · exact refined_log_source_259
  · exact refined_log_source_260
  · exact refined_log_source_261
  · exact refined_log_source_262
  · exact refined_log_source_263
  · exact refined_log_source_264
  · exact refined_log_source_265
  · exact refined_log_source_266
  · exact refined_log_source_267
  · exact refined_log_source_268
  · exact refined_log_source_269
  · exact refined_log_source_270
  · exact refined_log_source_271
  · exact refined_log_source_272
  · exact refined_log_source_273
  · exact refined_log_source_274
  · exact refined_log_source_275
  · exact refined_log_source_276
  · exact refined_log_source_277
  · exact refined_log_source_278
  · exact refined_log_source_279
  · exact refined_log_source_280
  · exact refined_log_source_281
  · exact refined_log_source_282
  · exact refined_log_source_283
  · exact refined_log_source_284
  · exact refined_log_source_285
  · exact refined_log_source_286
  · exact refined_log_source_287
  · exact refined_log_source_288
  · exact refined_log_source_289
  · exact refined_log_source_290
  · exact refined_log_source_291
  · exact refined_log_source_292
  · exact refined_log_source_293
  · exact refined_log_source_294
  · exact refined_log_source_295
  · exact refined_log_source_296
  · exact refined_log_source_297
  · exact refined_log_source_298
  · exact refined_log_source_299
  · exact refined_log_source_300

end LambdaCantor.Integer
