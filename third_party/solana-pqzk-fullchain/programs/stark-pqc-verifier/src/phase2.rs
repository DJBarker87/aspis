use anchor_lang::prelude::*;

use crate::state::{ChatMsg, CHAT_HEAD, ErrorCode, MAX_CHAT_PAYLOAD};

const PHASE2_MAX_CHAT_PAYLOAD: usize = 65_536;

#[derive(Accounts)]
pub struct Phase2InitChatMsg<'info> {
    /// CHECK: phase2-only preallocated account; must already be owned by this program.
    #[account(mut, owner = crate::ID)]
    pub chat_msg: UncheckedAccount<'info>,

    pub payer: Signer<'info>,
}

pub fn handle_phase2_init_chat_msg(
    ctx: Context<Phase2InitChatMsg>,
    recipient: Pubkey,
    cipher_len: u32,
    kem_len: u32,
    nonce: [u8; 12],
    slot: u64,
    payload_len: u32,
) -> Result<()> {
    require!(
        payload_len as usize <= PHASE2_MAX_CHAT_PAYLOAD,
        ErrorCode::LenMismatch
    );
    require!(
        (cipher_len as usize).saturating_add(kem_len as usize) <= payload_len as usize,
        ErrorCode::LenMismatch
    );
    require!(
        ctx.accounts.chat_msg.data_len() >= 8 + CHAT_HEAD + payload_len as usize,
        ErrorCode::LenMismatch
    );

    let chat = ChatMsg {
        sender: ctx.accounts.payer.key(),
        recipient,
        cipher_len,
        kem_len,
        nonce,
        slot,
        sig_pda: Pubkey::default(),
        sig_len: 0,
        sig_hash: [0u8; 32],
        payload: vec![0u8; payload_len as usize],
    };
    let mut data = ctx.accounts.chat_msg.try_borrow_mut_data()?;
    let mut writer = &mut data[..];
    chat.try_serialize(&mut writer)?;
    if payload_len as usize > MAX_CHAT_PAYLOAD {
        msg!(
            "phase2 loader payload {} exceeds production MAX_CHAT_PAYLOAD {}",
            payload_len,
            MAX_CHAT_PAYLOAD
        );
    }
    Ok(())
}

#[derive(Accounts)]
pub struct Phase2WriteChatMsgChunk<'info> {
    #[account(mut, owner = crate::ID)]
    pub chat_msg: Account<'info, ChatMsg>,
}

pub fn handle_phase2_write_chat_msg_chunk(
    ctx: Context<Phase2WriteChatMsgChunk>,
    offset: u32,
    data: Vec<u8>,
) -> Result<()> {
    require!(data.len() <= 900, ErrorCode::LenMismatch);

    let chat = &mut ctx.accounts.chat_msg;
    let start = offset as usize;
    let end = start.saturating_add(data.len());
    require!(end <= chat.payload.len(), ErrorCode::LenMismatch);
    chat.payload[start..end].copy_from_slice(&data);
    Ok(())
}
